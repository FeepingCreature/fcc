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

void testParams(ref Transaction t, void delegate(string) dg) {
  with (Transaction.Kind) switch (t.kind) {
    case SAlloc, SFree, FloatMath, FloatSwap: return;
    case Call, Nevermind, FloatStore, FloatPop, Pop: dg(t.dest); return;
    case FloatLoad, Push: dg(t.source); return;
    case LoadAddress, Mov, Mov2, Mov1: dg(t.from); dg(t.to); return;
    case Compare, MathOp: dg(t.op1); dg(t.op2); return;
    case Label, Jump: return;
    default: break;
  }
  assert(false, Format("huh? ", t));
}

 bool referencesStack(ref Transaction t, bool affects = false, bool active = false) {
  with (Transaction.Kind)
    if (t.kind == SAlloc /or/ SFree /or/ Call /or/ Compare /or/ Label /or/ Jump)
      return true;
    else if (t.kind == FloatMath /or/ FloatSwap)
      return false;
    else if (affects && t.kind == Pop /or/ Push)
      return true;
  bool res;
  testParams(t, delegate void(string s) {
    if (s.find("%esp") != -1) { res = res || true; return; }
    if (active) {
      int offs;
      if (s.isIndirect2(offs) == "%ebp") {
        res = res || offs < 0; // negative ebp is active stack
      }
    } else {
      res = res || s.find("%ebp") != -1;
    }
  });
  return res;
}

bool affectsStack(ref Transaction t) { return referencesStack(t, true); }

bool changesESP(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ Pop);
}

bool changesOrNeedsActiveStack(ref Transaction t) {
  return referencesStack(t, true, true);
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
    return !!(t.kind == Mov /or/ Mov2 /or/ Mov1 /or/ LoadAddress);
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

// dg, name, allow
Stuple!(bool delegate(Transcache, ref int[string]), string, bool)[] opts;
bool optsSetup;

bool isUtilityRegister(string reg) {
  if (reg == "%eax" /or/ "%ebx" /or/ "%ecx" /or/ "%edx")
    return true;
  return false;
}

bool pinsRegister(ref Transaction t, string reg) {
  with (Transaction.Kind)
    if (t.kind == Call /or/ Label /or/ Jump)
      return true;
    else if (t.kind == FloatMath /or/ FloatSwap)
      return false;
  bool res;
  testParams(t, delegate void(string s) {
    if (s.find(reg) != -1) res = true;
  });
  return res;
}

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
  string callDest;
  // not safe to mix foo(%ebp) and foo(%esp) in the same proc chunk
  int ebp_mode = -1;
  int eaten;
  bool noStack; // assumed no stack use; don't challenge this
  string toString() {
    return Format("cpu(", isValid?"[OK]":"[BAD]", " ", known, ", stack ", stack.length, "; ", stack, ", pop ", latepop, ", used ", use.keys, ", nvm ", nvmed, ")");
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
    bool canOverwrite(string s, string whs = null) {
      if (s in known && known[s] == whs) return true;
      foreach (entry; stack)
        if (entry.find(s) != -1) return false;
      foreach (key, value; known) {
        if (value.find(s) != -1) return false;
      }
      return true;
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
        if (val) { // if val is null, this is equivalent to void assignment. do nothing.
          if (mem.isRelative() && val.isRelative())
            return false;
          known[mem] = val;
        } else return false;
      }
      nvmed.remove(mem);
      return true;
    }
    if (t.kind != Transaction.Kind.Nevermind) {
      if (callDest)      return false;
      if (latepop && t.kind != Transaction.Kind.Pop)
                         return false;
      if (floatldsource) return false;
    }
    with (Transaction.Kind) switch (t.kind) {
      case Compare: return false;
      case LoadAddress:
        if (t.to.isRegister()) {
          int delta;
          if (auto reg = t.from.isIndirect2(delta)) {
            set(t.to, Format("+(", reg, ", $", delta, ")"));
            mixin(Success);
          }
        }
        break;
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
          // fallback
          known[t.op2] = null;
          mixin(Success);
          // break;
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
        if (t.size == 4) {
          stack ~= null;
          mixin(Success);
        } else break;
      case SFree:
        if (t.size % nativePtrSize != 0) return false;
        auto st2 = stack;
        for (int i = 0; i < t.size / nativePtrSize; ++i)
          if (st2.length) st2 = st2[0 .. $-1];
          else return false;
        stack = st2;
        mixin(Success);
      case Mov:
        if (t.to == "%esp")
          return false;
        
        if (t.from == "%esp")
          return false; // TODO: can this ever be handled?
        if (!canOverwrite(t.to, t.from)) break; // lol
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
          if (deref == "%esp" && t.to.isUtilityRegister() && !(delta % 4)) {
            auto from_rel = delta / 4;
            if (stack.length >= from_rel + 1) {
              auto val = stack[$ - 1 - from_rel];
              if (!set(t.to, val))
                return false;
              mixin(Success);
            }
            if (!stack.length && t.to.isUtilityRegister()) {
              if (!set(t.to, t.from))
                return false;
              noStack = true;
              mixin(Success);
            }
          }
          if (t.to.isUtilityRegister() && !(deref in known) && deref != "%esp") {
            if (!set(t.to, t.from))
              return false;
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
        if ("%esp" in use) // some other instr is relying on esp to stay unchanged
          return false;
        if (noStack)
          return false;
        if (t.type.size == nativePtrSize) {
          int offs;
          if (auto src = t.source.isIndirect2(offs)) {
            if (src in known) {
              if (auto indir = mkIndirect(known[src], offs)) {
                stack ~= indir;
                mixin(Success);
              }
            }
          }
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
        int offs;
        if (auto dest = t.dest.isIndirect2(offs)) {
          if (dest in known) {
            if (auto indir = mkIndirect(known[dest], offs)) {
              // if (!stack.length && latepop.length) break;
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
        nvmed[t.dest] = true;
        if (!(t.dest in use)) {
          if (t.dest in known) use[t.dest] = true;
          known.remove(t.dest);
        }
        mixin(Success);
      case Call:
        auto dest = t.dest;
        if (dest in known && known[dest].startsWith("$")) {
          callDest = "$" ~ known[dest][1..$];
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
      if (!value) return false; // #INV
      if (value.startsWith("+("))
        if (!mem.isRegister())
          return false;
        else if (value.find("gs") != -1)
          return false;
        else
          continue;
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
    assert(!stack.length || !noStack);
    foreach (entry; stack) {
      addTransaction(Transaction.Kind.Push, (ref Transaction t) {
        t.source = entry;
        t.type = Single!(SysInt);
      });
    }
    foreach (reg, value; known) {
      if (reg in nvmed) continue;
      if (auto indir = mkIndirect(value)) {
        addTransaction(Transaction.Kind.LoadAddress, (ref Transaction t) {
          t.from = indir; t.to = reg;
        });
      } else {
        addTransaction(Transaction.Kind.Mov, (ref Transaction t) {
          t.from = value; t.to = reg;
        });
      }
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
    /*foreach (key, value; nvmed) {
      addTransaction(Transaction.Kind.Nevermind, (ref Transaction t) {
        t.dest = key;
      });
    }*/
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
  mixin(opt("sort_mem", `*, ^SAlloc || ^SFree:
    !affectsStack($0)
    =>
    int delta;
    if ($1.kind == $TK.SAlloc) delta = $1.size;
    else if ($1.kind == $TK.SFree) delta = -$1.size;
    else assert(false);
    auto t2 = $0;
    if (t2.hasStackdepth) t2.stackdepth += delta;
    $SUBST([$1, t2]);
  `));
  mixin(opt("sort_pointless_mem", `*, ^SAlloc || ^SFree:
    (hasSource($0) || hasDest($0) || hasFrom($0) || hasTo($0))
    =>
    int shift = -1;
    $T t = $0.dup;
    bool dontDoIt;
    void detShift(string s) {
      if (s.between("(", ")") != "%esp") {
        int offs;
        if (s.isIndirect2(offs) == "%ebp" && offs < 0)
          dontDoIt = true; // may refer to stack-in-use
        if (s == "%esp") dontDoIt = true; // duh
        return;
      }
      auto offs = s.between("", "(").atoi();
      if ($1.kind == $TK.SAlloc) {
        shift = $1.size; // move it all to front
      } else {
        if (shift == -1) {
          shift = min($1.size, offs);
        } else {
          shift = min(shift, offs);
        }
      }
    }
    void applyShift(ref string s) {
      if (s.between("(", ")") != "%esp") return;
      auto offs = s.between("", "(").atoi();
      if ($1.kind == $TK.SAlloc) {
        s = Format(offs + shift, "(%esp)");
      } else {
        s = Format(offs - shift, "(%esp)");
      }
    }
    if (hasSource($0)) detShift(t.source);
    if (hasDest  ($0)) detShift(t.dest);
    if (hasFrom  ($0)) detShift(t.from);
    if (hasTo    ($0)) detShift(t.to);
    // ------------------------------
    if (hasSource($0)) applyShift(t.source);
    if (hasDest  ($0)) applyShift(t.dest);
    if (hasFrom  ($0)) applyShift(t.from);
    if (hasTo    ($0)) applyShift(t.to);
    bool substed;
    // override conas
    if ((!changesOrNeedsActiveStack($0) || $0.kind == $TK.Mov) && (shift > 0 || shift == -1 && !dontDoIt)) {
      if (shift == -1) shift = $1.size;
      auto t0 = $1, t2 = $1;
      t0.size = shift; t2.size -= shift;
      if (t.hasStackdepth)
        if ($1.kind == $TK.SAlloc)
          t.stackdepth += shift;
        else
          t.stackdepth -= shift;
      $T[] res = [t];
      if (t0.size) res = [t0] ~ res;
      if (t2.size) res = res ~ [t2];
      if (t0.size) {
        $SUBST(res);
        substed = true;
      }
    }
    // if (!substed) logln("sort_pointless_mem: ", [$0, $1], ", shift of ", shift, " dontDoIt is ", dontDoIt, " conas is ", changesOrNeedsActiveStack($0));
  `));
  /+
  bad
  mixin(opt("sort_any_util_reg_mov", `*, ^Mov:
    $0.kind != $TK.Mov && $1.to.isUtilityRegister()
    =>
    auto t1 = $0.dup, t2 = $1.dup;
    if (!pinsRegister($0, $1.to))
      $SUBST([t2, t1]);
  `));+/
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
  mixin(opt("fold_add_push", `^MathOp, ^Push:
    $0.opName == "addl" && $0.op1.isNumLiteral() && $0.op2.isUtilityRegister() &&
    $1.source.isIndirect() == $0.op2
    =>
    auto t1 = $0.dup, t2 = $1.dup;
    int offs;
    auto reg = $1.source.isIndirect2(offs);
    t2.source = Format(offs + $0.op1.literalToInt(), "(", reg, ")");
    $SUBST([t2, t1]);
  `));
  mixin(opt("scratch_mov", `^Mov, ^Call:
    $1.dest.isLiteral() && $0.to.isUtilityRegister()
    =>
    $SUBST([$1]);
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
  mixin(opt("silly_mov", `^Mov, ^Mov:
    $0.to == $1.from && $1.to == $0.from
    &&
    $0.to.isRegister()
    =>
    $SUBST([$0]);
  `));
  mixin(opt("silly_push", `^Push, ^Mov, ^SFree:
    $0.type.size == 4 && $1.to.isRegister() && $2.size > 4
    && $1.from == "(%esp)"
    =>
    int delta;
    if ($0.source.isIndirect2(delta) == "%ebp" && delta >= 0) {
      $T t1 = $2, t2 = $2;
      t1.size -= 4; t2.size = 4;
      $SUBST([t1, $0, $1, t2]);
    }
  `));
  mixin(opt("silly_push_2", `^Push, ^SFree:
    $0.type.size == 4 && $1.size > 4
    =>
    auto t = $1.dup;
    t.size -= 4;
    $SUBST([t]);
  `));
  mixin(opt("sort_nevermind", `*, ^Nevermind:
    $0.kind != $TK.Nevermind
    =>
    bool refsMe;
    with ($TK)
      if ($0.kind == Label /or/ Jump /or/ Call /or/ SAlloc /or/ SFree)
        refsMe = true;
      else testParams($0, (string s) { if (s.find($1.dest) != -1) refsMe = true; });
    if (!refsMe) {
      $SUBST([$1, $0]);
    }
  `));
  mixin(opt("combine_nevermind", `^Nevermind, ^Nevermind:
    $0.dest == $1.dest => $SUBST([$0]);
  `));
  mixin(opt("pop_mov_order", `^Pop, ^Mov:
    $0.type.size == 4 &&
    $0.dest == $1.from &&
    $1.to.isRegister() && !$1.from.isRegister()
    =>
    auto t1 = $0, t2 = $1;
    t1.dest = $1.to;
    t2.from = $1.to;
    t2.to = $0.dest;
    $SUBST([t1, t2]);
  `));
  mixin(opt("add_pop_order", `^MathOp, ^Nevermind, ^Pop:
    $0.opName == "addl" &&
    $0.op2 == "(%esp)" &&
    $2.dest == $0.op1
    =>
    $T t1 = $0, t2;
    swap(t1.op1, t1.op2);
    t2.kind = $TK.SFree;
    t2.size = 4;
    $SUBST([t1, t2]);
  `));
  bool isArgument(string s) {
    int offs;
    return s.isIndirect2(offs) == "%ebp" && offs >= 0;
  }
  // good luck working out what this is for
  mixin(opt("reorder_secretly", `^Mov, ^Mov, ^Push:
    $0.to.isUtilityRegister() &&
    $1.to.isUtilityRegister() &&
    $2.source.find($0.to) == -1 &&
    $0.from.isArgument()
    =>
    $SUBST([$1, $2, $0.dup]);
  `));
  mixin(opt("break_up_push", `^Push: $0.type.size > 4 && ($0.type.size % 4) == 0
    =>
    int delta;
    if (auto reg = $0.source.isIndirect2(delta)) {
      $T[] ts;
      for (int i = 0; i < $0.type.size / 4; ++i) {
        $T t;
        t.kind = $TK.Push;
        t.type = Single!(SysInt);
        t.source = Format(delta, "(", reg, ")");
        ts = t ~ ts;
        delta += 4;
      }
      $SUBST(ts);
    }
  `));
  mixin(opt("break_up_pop", `^Pop: $0.type.size > 4 && ($0.type.size % 4) == 0
    =>
    int delta;
    if (auto reg = $0.dest.isIndirect2(delta)) {
      $T[] ts;
      for (int i = 0; i < $0.type.size / 4; ++i) {
        $T t;
        t.kind = $TK.Pop;
        t.type = Single!(SysInt);
        t.dest = Format(delta, "(", reg, ")");
        ts ~= t;
        delta += 4;
      }
      $SUBST(ts);
    }
  `));
}

// Stuple!(bool delegate(Transcache, ref int[string]), string, bool)[] opts;
// what's necessary to uniquely identify an opt
string unique(string s) {
  string res;
  int count() {
    int c;
    foreach (entry; opts)
      if (!res || entry._1.startsWith(res)) c++;
    return c;
  }
  while (count > 1) {
    if (!s.length)
      return res; // give up
    res ~= s.take();
  }
  return res;
}
