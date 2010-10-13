module optimizer;

import assemble, tools.base, ast.base, ast.types;
alias asmfile.startsWith startsWith;

struct onceThenCall {
  void delegate(Transaction) dg;
  int opApply(int delegate(ref Transaction) _body) {
    Transaction tr;
    _body(tr);
    dg(tr);
    return 0;
  }
}

string opt(string name, string s) {
  string src = s.ctSlice("=>"), dest = s;
  string stmt_match = src.ctSlice(":");
  int instrs = 0;
  {
    string temp = stmt_match;
    while (temp.ctSlice(",").length) {
      src = src  .ctReplace("$"~ctToString(instrs), "match["~ctToString(instrs)~"]");
      dest = dest.ctReplace("$"~ctToString(instrs), "match["~ctToString(instrs)~"]");
      instrs ++;
    }
  }
  string res;
  res ~= `bool `~name~`(Transcache cache, ref int[string] labels_refcount) {
    bool changed;
    auto match = cache.findMatch("`~name~`", (Transaction[] list) {
      // logln("cond for `~name~`: ", list);
      if (list.length >= ` ~ ctToString(instrs);
  {
    string temp = stmt_match, merp; int i;
    while ((merp=temp.ctSlice(",")).length) {
      if (merp.ctStrip() == "*") i++;
      else
        res ~= ` && (` ~ merp.ctStrip().ctReplace("^", `list[` ~ ctToString(i++) ~ `].kind == Transaction.Kind.`) ~ `)`;
    }
  }
  res ~= `) {
        return ` ~ ctToString(instrs) ~ `;
      }
      else return 0;
    });
    if (match.length) _loophead:do {
      match.modded = false;`;
  if (src.ctStrip().length) res ~= `
      if (!(`~src~`)) continue;`;
  res ~= dest~`
      if (match.modded) {
        changed = true;
      }
    } while (match.advance());
    return changed;
  }
  opts ~= stuple(&`~name~`, "`~name~`", true);
  /* `~name~`();*/
  `;
  return res.ctReplace(
        "$SUBSTWITH", `foreach (ref $T res; onceThenCall(($T t) { match.replaceWith(t); })) with (res)`,
        "$SUBST", `match.replaceWith`,
        "$TK", `Transaction.Kind`,
        "$T", `Transaction`);
}

bool isRegister(string s) {
  return s.length > 2 && s[0] == '%' && s[1] != '(';
}

bool isLiteral(string s) {
  return s.length && s[0] == '$';
}

bool isNumLiteral(string s) {
  if (!s.isLiteral()) return false;
  foreach (ch; s[1 .. $])
    if (ch != '-' && (ch < '0' || ch > '9')) return false;
  return true;
}

int literalToInt(string s) {
  if (!isLiteral(s)) asm { int 3; }
  assert(isLiteral(s), "not a literal: "~s);
  return s[1 .. $].atoi();
}

bool referencesStack(ref Transaction t, bool affects = false) {
  bool foo(string s) { return s.find("%esp") != -1 || s.find("%ebp") != -1; }
  with (Transaction.Kind) switch (t.kind) {
    case   SAlloc, SFree            : return true;
    case                        Pop : if (affects) return true; return t.dest.foo();
    case                       Push : if (affects) return true; return t.source.foo();
    case                        Mov : return t.from.foo() || t.to.foo();
    case                     MathOp : return t.op1.foo() || t.op2.foo();
    case                  FloatLoad : return t.source.foo();
    case       FloatPop, FloatStore : return t.dest.foo();
    case       FloatMath, FloatSwap : return false;
    case Call, Compare, Label, Jump : return true; // not safe to move stuff past
    case                  Nevermind : return t.dest.foo();
    default: break;
  }
  assert(false, Format("huh? ", t));
}

bool affectsStack(ref Transaction t) { return referencesStack(t, true); }

bool changesESP(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ Pop);
}

bool hasSource(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ FloatLoad);
}

bool hasDest(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Pop /or/ Call /or/ FloatStore /or/ FloatPop);
}

bool hasFrom(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Mov /or/ Mov2 /or/ Mov1);
}
alias hasFrom hasTo;

bool willOverwrite(ref Transaction t, string what) {
  if (!what.isRegister()) return false;
  if (hasDest(t)) return t.dest == what;
  if (hasTo(t)) return t.to == what;
  return false;
}

bool hasSize(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ Pop /or/ Mov /or/ Mov2 /or/ Mov1);
}

int size(ref Transaction t) {
  with (Transaction.Kind) switch (t.kind) {
    case Push: return t.type.size;
    case Pop: return t.type.size;
    case Mov: return 4;
    case Mov2: return 2;
    case Mov1: return 1;
  }
  assert(false);
}

bool isMemRef(string s) {
  if (s.find("(") != -1) return true;
  if (s.startsWith("$")) return false;
  if (s == "%eax" /or/ "%ebx" /or/ "%ebp" /or/ "%ecx" /or/ "%edx") return false;
  if (s.startsWith("%gs:")) return true;
  return true;
}

// dg, name, allow
Stuple!(bool delegate(Transcache, ref int[string]), string, bool)[] opts;
bool optsSetup;

// track processor state
// obsoletes about a dozen peephole opts
class ProcTrack : ExtToken {
  string[string] known;
  string[] stack; // nativePtr-sized
  string[] latepop;
  string floatldsource; // TODO: fpu
  // in use by this set of transactions
  // emit before overwriting
  bool[string] use, nvmed;
  // backup
  Transaction[] backup, knownGood;
  int overfree;
  string callDest;
  // not safe to mix foo(%ebp) and foo(%esp) in the same proc chunk
  int ebp_mode = -1;
  int eaten;
  string toString() {
    return Format("cpu(", known, ", stack ", stack.length, "; ", stack, ", pop ", latepop, ", used ", use.keys, " valid ", isValid(), ")")
      ~ (overfree?Format(" overfree ", overfree):"");
  }
  bool update(Transaction t) {
    scope(exit) {
      if (isValid) {
        knownGood = translate();
        // nuh!
        // use = null; // effectively restarting
        backup = null;
      }
    }
    // #define .. lol
    const string Success = "{ backup ~= t; eaten ++; return true; }";
    string isIndirectSimple(string s) {
      if (s.length >= 2 && s[0] == '(' && s[$-1] == ')')
        return s[1..$-1];
      else return null;
    }
    string isIndirectComplex(string s, ref int delta) {
      if (s.between(")", "").length) return null;
      auto betw = s.between("(", ")");
      if (betw && betw.isRegister()) {
        delta = s.between("", "(").atoi();
        return betw;
      }
      return null;
    }
    string isIndirect2(string s, ref int delta) {
      delta = 0;
      if (auto res = isIndirectSimple(s)) return res;
      if (auto res = isIndirectComplex(s, delta)) return res;
      return null;
    }
    string isIndirect(string s) {
      int bogus;
      return isIndirect2(s, bogus);
    }
    string mkIndirect(string val, int delta = 0 /* additional delta */) {
      if (val.startsWith("+(")) {
        auto op2 = val.between("(", ")"), op1 = op2.slice(",").strip();
        op2 = op2.strip();
        if (op1.isRegister() && op2.isNumLiteral()) {
          auto op2i = op2.literalToInt();
          /*if (t.to in use)
            return null;*/
          // to indirect access
          return Format(op2i + delta, "(", op1, ")");
        }
      }
      return null;
    }
    bool used(string s) {
      foreach (entry; stack)
        if (entry.find(s) != -1) return true;
      foreach (key, value; known) {
        if (value.find(s) != -1) return true;
      }
      return false;
    }
    bool set(string mem, string val) {
      if (mem.find("esp") != -1) {
        if (ebp_mode == -1) ebp_mode = false;
        else if (ebp_mode == true) return false;
      }
      if (mem.find("ebp") != -1) {
        if (ebp_mode == -1) ebp_mode = true;
        else if (ebp_mode == false) return false;
      }
      if (mem == val) known.remove(mem);
      else {
        if (mem.isRelative() && val.isRelative())
          return false;
        known[mem] = val;
      }
      nvmed.remove(mem);
      return true;
    }
    if (t.kind != Transaction.Kind.Nevermind) {
      if (callDest)      return false;
      if (latepop)       return false;
      if (floatldsource) return false;
    }
    with (Transaction.Kind) switch (t.kind) {
      case Compare: return false;
      case MathOp:
        if (t.opName == "imull" && t.op1 == "$1"
         || t.opName == "addl" && t.op1 == "$0"
         || t.opName == "subl" && t.op1 == "$0") {
          mixin(Success);
        }
        string op2 = t.op2;
        if (auto p = op2 in known) op2 = *p;
        
        if (t.opName != "addl") break;
        if (t.op1.isNumLiteral() && t.op2 in known) {
          auto stuf = known[t.op2];
          if (stuf.isRegister()) {
            if (!set(t.op2, "+(" ~ known[t.op2] ~ ", " ~ t.op1 ~ ")"))
              return false;
            mixin(Success);
          } else if (t.op1.isNumLiteral() && stuf.startsWith("+(")) {
            auto mop2 = stuf.between("+(", ")"), mop1 = mop2.slice(", ");
            if (mop2.isNumLiteral()) {
              if (!set(t.op2, Format("+(",
                mop1,
                ", $", mop2.literalToInt() + t.op1.literalToInt(),
              ")")))
                return false;
              mixin(Success);
            }
          }
          break;
        }
        if (t.op1.isNumLiteral() && t.op2 == "(%esp)" && stack.length && stack[$-1].startsWith("+(")) {
          auto mop2 = stack[$-1].between("+(", ")"), mop1 = mop2.slice(", ");
          if (mop2.isNumLiteral()) {
            stack[$-1] = Format("+(", mop1, ", $", mop2.literalToInt() + t.op1.literalToInt(), ")");
            mixin(Success);
          }
        }
        break;
      case SAlloc:
        if (overfree) return false;
        if (t.size == 4) {
          stack ~= null;
          mixin(Success);
        } else break;
      case SFree:
        if (t.size % nativePtrSize != 0) return false;
        for (int i = 0; i < t.size / nativePtrSize; ++i)
          if (stack.length) stack = stack[0 .. $-1];
          else {
            if (latepop) return false;
            overfree += nativePtrSize;
          }
        mixin(Success);
      case Mov:
        if (t.to == "%esp")
          return false;
        
        if (t.from == "%esp")
          return false; // TODO: can this ever be handled?
        if (used(t.to)) break; // lol
        if (t.to.isIndirect() == "%esp")
          use["%esp"] = true;
        int delta;
        if (t.from.isRegister()) {
          string src = t.from;
          if (auto p = src in known)
            src = *p;
          if (src.isRegister())
            use[src] = true;
          if (t.to.isRegister()) {
            if (!set(t.to, src))
              return false;
          } else if (t.to == "(%esp)") {
            if (!stack.length) break;
            stack[$-1] = src;
          } else {
            if (!set(t.to, src))
              return false;
          }
          mixin(Success);
        } else if (t.from in known && known[t.from].isLiteral()) {
          if (!set(t.to, known[t.from]))
            return false;
          mixin(Success);
        } else if (auto deref = t.from.isIndirect2(delta)) {
          if (deref in nvmed) return false;
          if (deref in known) {
            auto val = known[deref];
            if (auto indir = mkIndirect(val, delta)) {
              if (!set(t.to, indir))
                return false;
              mixin(Success);
            }
          }
          // if (deref == "%esp") logln("delta ", delta, " to ", t.to, " and we are ", this);
          if (deref == "%esp" && t.to == "%eax" && !(delta % 4)) {
            auto from_rel = delta / 4;
            if (stack.length >= from_rel + 1) {
              auto val = stack[$ - 1 - from_rel];
              if (!set(t.to, val))
                return false;
              mixin(Success);
            }
          }
          if (t.to == "%eax" && !(deref in known) && deref != "%esp") {
            known[t.to] = t.from;
            use[deref] = true;
            mixin(Success);
          }
          return false;
          break;
        } else if (t.from.isLiteral()) {
          if (!set(t.to, t.from))
            return false;
          mixin(Success);
        }
        break;
      case Label: return false;
      case Push:
      restart_push:
        if (overfree)
          return false;
        /+static int xx;
        xx++;
        // 1727 .. 1728
        if (xx > 1728) return false;+/
        if ("%esp" in use) // some other instr is relying on esp to stay unchanged
          return false;
        if (t.type.size == nativePtrSize) {
          auto val = t.source;
          if (auto p = t.source in known)
            val = *p;
          // Be VERY careful changing this
          // remember, push is emat before mov!
          if (val in known) return false;
          /*if (auto reg = val.isIndirect())
            return false;*/
            // use[reg] = true; // broken
          if (val.isRegister()) use[val] = true;
          if (auto reg = val.isIndirect()) {
            if (reg in known) return false; // bad dependence ordering
            use[reg] = true;
          }
          stack ~= val;
          mixin(Success);
        }
        if (t.source.isLiteral()) {
          if (t.type.size % nativePtrSize != 0)
            return false; // not a case we can handle
          auto steps = t.type.size / nativePtrSize;
          for (int i = 0; i < steps; ++i)
            stack ~= t.source;
          mixin(Success);
        }
        if (t.type.size == nativePtrSize * 2) { // split into two pushes
          int offs;
          if (auto indir = isIndirect2(t.source, offs)) {
            t.type = Single!(SysInt);
            auto t2 = t;
            t2.source = Format(offs + 4, "(", indir, ")");
            if (!update(t2)) return false;
            goto restart_push;
          }
        }
        break;
      case Pop:
        if (t.type.size != nativePtrSize) return false;
        if (t.dest.isRegister()) {
          if (!stack.length) break;
          if (t.dest != stack[$-1]) {
            foreach (entry; stack)
              if (entry.find(t.dest) != -1) return false;
          }
          //   if (&& t.dest in use) return false;
          if (!set(t.dest, stack[$-1]))
            return false;
          stack = stack[0 .. $-1];
          mixin(Success);
        }
        if (auto dest = t.dest.isIndirectSimple()) {
          if (dest in known) {
            if (auto indir = mkIndirect(known[dest])) {
              if (!stack.length && latepop.length) break;
              if (stack.length) {
                if (!set(indir, stack[$-1]))
                  return false;
                stack = stack[0 .. $-1];
                mixin(Success);
              } else {
                latepop ~= indir;
                mixin(Success);
              }
            }
          }
          return false;
        }
        break;
      case Nevermind:
        if (!stack.length && !known.length)
          return false;
        bool useful;
        foreach (entry; stack)
          if (entry == t.dest) { useful = true; break; }
        foreach (reg, value; known)
          if (reg == t.dest) { useful = true; break; }
        if (useful) {
          nvmed[t.dest] = true;
          use[t.dest] = true; // don't reuse in this block (because nvm are emitted at the end)
        }
        mixin(Success);
      case Call:
        auto dest = t.dest;
        if (dest in known && known[dest].startsWith("$")) {
          callDest = "$" ~ known[dest][1..$];
          use[dest] = true;
          mixin(Success);
        }
        return false;
      case Jump: return false;
      case FloatLoad:
        if (auto src = t.source.isIndirectSimple()) {
          if (src in known) {
            if (auto indir = mkIndirect(known[src])) {
              floatldsource = indir;
              mixin(Success);
            }
          }
        }
        break;
      default: break;
    }
    return false;
    logln("---- Unsupported: ", t);
    logln("state ", this);
    assert(false);
  }
  bool isValid() {
    foreach (entry; stack) {
      if (entry.startsWith("+(")) return false;
      if (!entry.strip().length) return false;
    }
    foreach (mem, value; known) {
      if (mem in nvmed) continue;
      if (value.startsWith("+(")) return false;
      // TODO: move over eax or something
      if (mem.isRelative() && value.isRelative()) return false;
    }
    return true;
  }
  Transaction[] translate() {
    if (!isValid()) {
      return knownGood ~ backup;
    }
    Transaction[] res;
    void addTransaction(Transaction.Kind tk, void delegate(ref Transaction) dg) {
      Transaction t;
      t.kind = tk;
      dg(t);
      res ~= t;
    }
    foreach (entry; stack) {
      addTransaction(Transaction.Kind.Push, (ref Transaction t) {
        t.source = entry;
        t.type = Single!(SysInt);
      });
    }
    foreach (reg, value; known) {
      if (reg in nvmed) continue;
      addTransaction(Transaction.Kind.Mov, (ref Transaction t) {
        t.from = value; t.to = reg;
      });
    }
    if (overfree) {
      addTransaction(Transaction.Kind.SFree, (ref Transaction t) {
        t.size = overfree;
      });
    }
    foreach (entry; latepop) {
      addTransaction(Transaction.Kind.Pop, (ref Transaction t) {
        t.dest = entry;
        t.type = Single!(SysInt);
      });
    }
    if (callDest) {
      addTransaction(Transaction.Kind.Call, (ref Transaction t) {
        t.dest = callDest;
      });
    }
    if (floatldsource) {
      addTransaction(Transaction.Kind.FloatLoad, (ref Transaction t) {
        t.source = floatldsource;
      });
    }
    foreach (key, value; nvmed) {
      addTransaction(Transaction.Kind.Nevermind, (ref Transaction t) {
        t.dest = key;
      });
    }
    return res;
  }
  string toAsm() { assert(false); }
}

bool delegate(Transcache, ref int[string]) ext_step;

void setupOpts() {
  if (optsSetup) return;
  optsSetup = true;
  bool goodMovSize(int i) { return i == 4 || i == 2 || i == 1; }
  mixin(opt("ext_step", `*, *
    =>
    ProcTrack obj;
    $T t;
    t.kind = $TK.Extended;
    if ($0.kind == $TK.Extended) {
      obj = cast(ProcTrack) $0.obj;
      t.obj = obj;
      bool couldUpdate = obj.update($1);
      if (couldUpdate) {
        $SUBST([t]);
        if (match.to != match.parent.list.length) {
          goto skip; // > > > \
        } //                  v
      } //                    v
      auto res = obj./*       v */translate();
      bool progress = /*      v */res.length != obj.eaten;
      if (!couldUpdate) res/* v */ ~= $1;
      $SUBST(res); //         v
      if (!progress) //       v
        match.modded = /*     v */ false; // meh. just skip one
      changed = progress; //  v secretly
      skip:; //   < < < < < < /
    } else {
      New(obj);
      t.obj = obj;
      if (obj.update($0)) { $SUBST([t, $1]); }
      // else logln("Reject ", $0, ", ", $1);
    }
  `));
  // .ext_step = &ext_step; // export
  // opts = opts[0 .. $-1]; // only do ext_step once
  
  mixin(opt("rewrite_zero_ref", `*:
    hasSource($0) || hasDest($0) || hasFrom($0) || hasTo($0)
    =>
    auto t = $0;
    if (hasSource(t) && t.source.startsWith("0("))
      { t.source = t.source[1..$]; $SUBST([t]); }
    if (hasDest  (t) && t.dest  .startsWith("0("))
      { t.dest   = t.dest  [1..$]; $SUBST([t]); }
    if (hasFrom  (t) && t.from  .startsWith("0("))
      { t.from   = t.from  [1..$]; $SUBST([t]); }
    if (hasTo    (t) && t.to    .startsWith("0("))
      { t.to     = t.to    [1..$]; $SUBST([t]); }
  `));
  // alloc/free can be shuffled down past _anything_ that doesn't reference stack.
  mixin(opt("sort_mem", `^SAlloc || ^SFree, *:
    !affectsStack($1)
    =>
    int delta;
    if ($0.kind == $TK.SAlloc) delta = $0.size;
    else if ($0.kind == $TK.SFree) delta = -$0.size;
    else assert(false);
    auto t2 = $1;
    if (t2.hasStackdepth) t2.stackdepth -= delta;
    $SUBST([t2, $0]);
  `));
  mixin(opt("sort_pointless_mem", `^SAlloc || ^SFree, *:
    (hasSource($1) || hasDest($1) || hasFrom($1) || hasTo($1)) && !changesESP($1)
    =>
    string* sp;
    $T t = $1.dup;
    bool used;
    void doStuff(ref string s) {
      if (s.between("(", ")") != "%esp") return;
      auto offs = s.between("", "(").atoi();
      if ($0.kind == $TK.SAlloc) {
        if (offs > $0.size) { // will be unaffected
          s = Format(offs - $0.size, "(%esp)");
          used =  true;
        }
      } else {
        s = Format(offs + $0.size, "(%esp)");
        used = true;
      }
    }
    if (hasSource($1)) doStuff(t.source);
    if (hasDest  ($1)) doStuff(t.dest);
    if (hasFrom  ($1)) doStuff(t.from);
    if (hasTo    ($1)) doStuff(t.to);
    if (used)
      $SUBST([t, $0]);
  `));
  mixin(opt("collapse_alloc_frees", `^SAlloc || ^SFree, ^SAlloc || ^SFree =>
    int sum_inc;
    if ($0.kind == $TK.SAlloc) sum_inc += $0.size;
    else sum_inc -= $0.size;
    if ($1.kind == $TK.SAlloc) sum_inc += $1.size;
    else sum_inc -= $1.size;
    if (!sum_inc) $SUBST(null);
    else $SUBSTWITH {
      if (sum_inc > 0) kind = $TK.SAlloc;
      else kind = $TK.SFree;
      size = abs(sum_inc);
    }
  `));
  mixin(opt("pointless_free", `^SFree, ^Push:
    $0.size == $1.type.size && $0.size == 4 && !isMemRef($1.source) && $1.source != "%esp"
    =>
    $SUBSTWITH {
      kind = $TK.Mov;
      from = $1.source;
      to = "(%esp)";
    }
  `));
  mixin(opt("collapse_push_pop", `^Push, ^Pop:
    ($0.type.size == $1.type.size) && (!$0.source.isMemRef() || !$1.dest.isMemRef())
    =>
    if ($0.source == $1.dest) { /*logln("Who the fuck produced this retarded bytecode: ", match[]);*/ $SUBST(null); continue; }
    $T[] movs;
    int size = $0.type.size;
    string source = $0.source, dest = $1.dest;
    void incr(ref string s, int sz) {
      if (s.length && !s.startsWith("$") && !s.startsWith("%") && !s.startsWith("(")) {
        // num(reg)
        auto num = s.slice("(").atoi();
        s = Format(num + sz, "(", s);
        return;
      }
      if (s.length && s[0] == '$') { // number; repeat
        return;
      }
      logln(":: ", s, "; ", $0.source, " -> ", $1.dest);
      assert(false, "2");
    }
    void doMov($TK kind, int sz) {
      while (size >= sz) {
        $T mv;
        mv.kind = kind;
        mv.from = source; mv.to = dest;
        mv.stackdepth = $0.stackdepth;
        size -= sz;
        if (size) {
          source.incr(sz);
          dest.incr(sz);
        }
        movs ~= mv;
      }
    }
    doMov($TK.Mov, 4);
    doMov($TK.Mov2, 2);
    doMov($TK.Mov1, 1);
    $SUBST(movs);
  `));
  mixin(opt("add_mov", `^MathOp, ^Mov: $0.opName == "addl" && $0.op2 == "%eax" && $0.op2 == $1.from && $0.op1 == $1.to =>
    $SUBSTWITH {
      kind = $TK.MathOp;
      opName = $0.opName; op1 = "%eax"; op2 = $0.op1;
    }
  `));
  mixin(opt("fold_math", `^Mov, ^MathOp: $1.opName == "addl" && $0.to == $1.op2 && $0.from.isNumLiteral() && $1.op1.isNumLiteral() =>
    $SUBSTWITH {
      kind = $TK.Mov;
      from = Format("$", $0.from.literalToInt() + $1.op1.literalToInt());
      to = $0.to;
    }
  `));
  mixin(opt("merge_literal_adds", `^MathOp, ^MathOp:
    $0.opName == "addl" && $1.opName == "addl" &&
    $0.op1.isNumLiteral() && $1.op1.isNumLiteral() &&
    $0.op2 == "%eax" && $1.op2 == "%eax"
    =>
    $SUBSTWITH {
      kind = $TK.MathOp;
      opName = "addl";
      op1 = Format("$", $0.op1.literalToInt() + $1.op1.literalToInt());
      op2 = "%eax";
    }
  `));
  mixin(opt("load_from_push", `^Push, ^FloatLoad:
    !$0.source.isRegister() && $1.source == "(%esp)"
    =>
    $T a1 = $1.dup, a2, a3;
    a1.source = $0.source;
    if ($1.hasStackdepth) a1.stackdepth = $1.stackdepth - 4;
    a2.kind = $TK.Nevermind;
    a2.dest = $0.source;
    a3.kind = $TK.SAlloc;
    a3.size = 4;
    $SUBST([a1, a2, a3]);
  `));
  mixin(opt("fold_float_pop_load", `^FloatPop, ^FloatLoad, ^SFree: $0.dest == $1.source && $0.dest == "(%esp)" && $2.size == 4 => $SUBST([$2]);`));
  mixin(opt("fold_float_pop_load_to_store", `^FloatPop, ^FloatLoad: $0.dest == $1.source => $SUBSTWITH { kind = $TK.FloatStore; dest = $0.dest; }`));
  mixin(opt("make_call_direct", `^Mov, ^Call: $0.to == $1.dest => $SUBSTWITH { kind = $TK.Call; dest = $0.from; } `));
  
  mixin(opt("ebp_to_esp", `*:
    (  hasSource($0) && $0.source.between("(", ")") == "%ebp"
    || hasDest  ($0) && $0.dest  .between("(", ")") == "%ebp"
    || hasFrom  ($0) && $0.from  .between("(", ")") == "%ebp"
    )
    && $0.hasStackdepth && (!hasSize($0) || size($0) != 1)
    =>
    $T t = $0;
    void doStuff(ref string str) {
      auto offs = str.between("", "(").atoi(); 
      auto new_offs = offs + t.stackdepth;
      if (new_offs) str = Format(new_offs, "(%esp)");
      else str = "(%esp)";
      $SUBST([t]);
    }
    bool skip;
    if ($0.kind == $TK.Push /or/ $TK.Pop) {
      // if we can't do the push in one step
      if ($0.type.size != 4 /or/ 2 /or/ 1) 
        skip = true;
    }
    if (!skip) {
      if (hasSource(t) && t.source.between("(", ")") == "%ebp") doStuff(t.source);
      if (hasDest  (t) && t.dest  .between("(", ")") == "%ebp") doStuff(t.dest);
      if (hasFrom  (t) && t.from  .between("(", ")") == "%ebp") doStuff(t.from);
      if (hasTo    (t) && t.to    .between("(", ")") == "%ebp") doStuff(t.to);
    }
  `));
  
  // jump opts
  mixin(opt("join_labels", `^Label, ^Label => auto t = $0; t.names = t.names ~ $1.names; $SUBST([t]); `));
  mixin(opt("pointless_jump", `^Jump, ^Label:
    $1.hasLabel($0.dest)
    =>
    labels_refcount[$0.dest] --;
    $SUBST([$1]);
  `));
  mixin(opt("silly_mov", `^Mov, ^Mov: $0.to == $1.from && $1.to == $0.from && $0.to.isRegister() => $SUBST([$1]); `));
}

// Stuple!(bool delegate(Transcache, ref int[string]), string, bool)[] opts;
// what's necessary to uniquely identify an opt
string unique(string s) {
  string res;
  int count() {
    int c;
    foreach (entry; opts)
      if (entry._1.startsWith(res)) c++;
    return c;
  }
  while (count > 1) {
    if (!s.length)
      return res; // give up
    res ~= s.take();
  }
  return res;
}
