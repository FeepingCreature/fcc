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

// reference form
string cleanup(string s) {
  if (auto rest = s.startsWith("0(")) return "("~rest;
  return s;
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
    bool _changed;
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
        _changed = true;
      }
    } while (match.advance());
    return _changed;
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

void accessParams(ref Transaction t, void delegate(ref string) dg, bool writeonly = false) {
  with (Transaction.Kind) switch (t.kind) {
    case SAlloc, SFree,
      FloatMath, FPSwap  : return;
    case Call, Nevermind,
      FloatStore, DoubleStore,
      FloatPop, DoublePop,
      Pop                   : dg(t.dest); return;
    case ExtendDivide:
      string eax = "%eax";
      dg(eax);
      if (eax != "%eax") { logln("broke implicit reg dep => ", eax); asm { int 3; } }
      if (!writeonly) dg(t.source);
      return;
    case FloatLoad, DoubleLoad, RealLoad, RegLoad, FloatCompare,
      FloatIntLoad, Push    : if (!writeonly) dg(t.source); return;
    case LoadAddress,
      Mov, Mov2, Mov1       : if (!writeonly) dg(t.from); dg(t.to); return;
    case Compare,
      MathOp, SSEOp         : if (!writeonly) dg(t.op1); dg(t.op2); return;
    case Label, Jump        : return;
    default                 : break;
  }
  logln("huh? ", t);
  fail();
}

struct TransactionInfo {
  Transaction* tp;
  const string Table = `
    name | inOp1     | inOp2    | getOutOp | size         | accessParams
    ------------------------------------------------------------------
    Push | &#.source | ø        | ø        | #.type.size  | if (!wo) dg(#.source);
  `;
  int numInOps() {
    mixin(
      `switch (tp.kind) { `
      ~ ctTableUnroll(Table, `case Transaction.Kind.$name:
        static if ("$inOp1" == "ø") { static if ("$inOp2" == "ø") return 0; else return 1; }
        else { static if ("$inOp2" == "ø") return 1; else return 2; }
        `)
      ~ `default: logln("but what about ", tp.kind); asm { int 3; }
    }`);
  }
  string inOp1() {
    mixin(
      `switch (tp.kind) { `
      ~ ctTableUnroll(Table, `case Transaction.Kind.$name:
        static if ("$inOp1" == "ø") { logln("No input operand for $name! "); asm { int 3; } }
        else return *mixin("$inOp1".ctReplace("#", "(*tp)"));
        `)
      ~ `default: logln("but what about ", tp.kind); asm { int 3; }
    }`);
  }
  string inOp1(string s) {
    mixin(
      `switch (tp.kind) { `
      ~ ctTableUnroll(Table, `case Transaction.Kind.$name:
        static if ("$inOp1" == "ø") { logln("No input operand for $name! "); asm { int 3; } }
        else return mixin("*$inOp1 = s".ctReplace("#", "(*tp)"));
        `)
      ~ `default: logln("but what about ", tp.kind); asm { int 3; }
    }`);
  }
  int opSize() {
    mixin(
      `switch (tp.kind) { `
      ~ ctTableUnroll(Table, `case Transaction.Kind.$name:
        return mixin("$size".ctReplace("#", "(*tp)"));
        `)
      ~ `default: logln("but what about ", tp.kind); asm { int 3; }
    }`);
  }
  bool hasOutOp() {
    mixin(
      `switch (tp.kind) { `
      ~ ctTableUnroll(Table, `case Transaction.Kind.$name:
        static if ("$getOutOp" == "ø") return false;
        else return true;
        `)
      ~ `default: logln("but what about ", tp.kind); asm { int 3; }
    }`);
  }
  bool hasOps() { return numInOps || hasOutOp; }

  string* getDstp(ref Transaction t) {
    with (Transaction.Kind) switch (t.kind) {
      case Pop, Call, FloatStore, DoubleStore,
        FloatPop, DoublePop, Nevermind: return &t.dest;
      case Mov, Mov1, Mov2, LoadAddress: return &t.to;
      case MathOp, SSEOp: return &t.op2;
      case Label, SAlloc, SFree, Jump, FloatLoad, DoubleLoad: return null;
      case Push, Compare: return null;
      case FloatMath, FloatIntLoad, FloatCompare,
        RegLoad, FPSwap, ExtendDivide: return null;
      default: logln("huh? dstp ", t); asm { int 3; }
    }
  }

  string getDst(ref Transaction t) {
    if (t.kind == Transaction.Kind.Push) return "(%esp)";
    if (auto p = getDstp(t)) return *p;
    return null;
  }
  
  int opSize(ref Transaction t) {
    if (hasSize(t)) return t.size;
    with (Transaction.Kind) {
      switch (t.kind) {
        case Mov, LoadAddress, FloatStore, FloatPop, FloatLoad: return 4;
        case DoubleStore, DoublePop, DoubleLoad: return 8;
        case SSEOp: return 16;
        case Mov2: return 2;
        case Mov1: return 1;
        case Push, Pop: return t.type.size;
        case SFree, SAlloc: return t.size;
        case Call, Nevermind: return -1;
        default: break;
      }
    }
    logln("Does ", t, " has size? ");
    asm { int 3; }
  }
}

TransactionInfo info(ref Transaction t) {
  TransactionInfo res;
  res.tp = &t;
  return res;
}

 bool referencesStack(ref Transaction t, bool affects = false, bool active = false) {
  with (Transaction.Kind)
    if (t.kind == SAlloc /or/ SFree /or/ Call /or/ Compare /or/ Label /or/ Jump)
      return true;
    else if (t.kind == FloatMath /or/ FPSwap)
      return false;
    else if (affects && t.kind == Pop /or/ Push)
      return true;
  bool res;
  void test(ref string s) {
    if (s.isIndirect()) res |= true; // MAY access the stack.
    if (s.find("%esp") != -1) { res |= true; return; }
    if (active) {
      int offs;
      if (s.isIndirect2(offs) == "%ebp") {
        res |= offs < 0; // negative ebp is active stack
      }
    } else {
      res |= s.find("%ebp") != -1;
    }
  }
  if (affects) accessParams(t, &test, true);
  else         accessParams(t, &test);
  return res;
}

bool affectsStack(ref Transaction t) { return referencesStack(t, true); }

bool changesOrNeedsActiveStack(ref Transaction t) {
  return referencesStack(t, false, true) || referencesStack(t, true, true);
}

bool willOverwrite(ref Transaction t, string what) {
  if (!what.isRegister()) return false;
  bool res;
  accessParams(t, (ref string s) { res |= s == what; }, true);
  return res;
}

bool hasSize(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ Pop /or/ Mov /or/ Mov2 /or/ Mov1 /or/ SFree /or/ SAlloc);
}

bool collide(string a, string b) {
  if (auto ia = a.isIndirect()) a = ia;
  if (auto ib = b.isIndirect()) b = ib;
  return (a == b);
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

bool isUtilityRegister(string reg) {
  if (reg == "%eax" /or/ "%ebx" /or/ "%ecx" /or/ "%edx")
    return true;
  return false;
}

bool pinsRegister(ref Transaction t, string reg) {
  with (Transaction.Kind)
    if (t.kind == Call /or/ Label /or/ Jump)
      return true;
    else if (t.kind == FloatMath /or/ FPSwap)
      return false;
  bool res;
  accessParams(t, delegate void(ref string s) {
    if (s.find(reg) != -1) res = true;
  });
  return res;
}

void fixupString(ref string s, int shift) {
  if (auto rest = s.startsWith("+(%esp, ")) {
    s = qformat("+(%esp, $",
      rest.between("$", ")").atoi() + shift,
      ")"
    );
  }
  int offs;
  if ("%esp" == s.isIndirect2(offs)) {
    if (offs + shift < 0) {
      logln("Tried to fix up ", s, " by ", shift, " into negative! ");
      asm { int 3; }
    }
    s = qformat(offs + shift, "(%esp)").cleanup();
  }
}

struct OrderedHashlike(K, V) {
  Stuple!(K, V)[] array;
  V* opIn_r(K k) {
    foreach (ref entry; array)
      if (entry._0 == k) return &entry._1;
    return null;
  }
  string toString() { return Format(array); }
  V opIndex(K k) {
    if (auto p = opIn_r(k)) return *p;
    logln("No such key: ", k, ", in ", array);
    asm { int 3; }
  }
  void opIndexAssign(V v, K k) {
    if (auto p = opIn_r(k)) { *p = v; return; }
    array ~= stuple(k, v);
  }
  int length() { return array.length; }
  int opApply(int delegate(ref K, ref V) dg) {
    foreach (entry; array)
      if (auto res = dg(entry._0, entry._1)) return res;
    return 0;
  }
  int find(K k) {
    foreach (i, e; array) if (e._0 == k) return i;
    return -1;
  }
  void remove(K k) {
    while (true) {
      auto pos = find(k);
      if (pos == -1) return;
      array = array[0 .. pos] ~ array[pos+1 .. $];
    }
  }
}

// track processor state
// obsoletes about a dozen peephole opts
class ProcTrack : ExtToken {
  OrderedHashlike!(string, string) known;
  string[] stack; // nativePtr-sized
  string[] latepop;
  // in use by this set of transactions
  // emit before overwriting
  bool[string] use, nvmed;
  // backup
  Transaction[] backup, knownGood;
  // not safe to mix foo(%ebp) and foo(%esp) in the same proc chunk
  int ebp_mode = -1;
  int eaten;
  bool noStack; // assumed no stack use; don't challenge this
  int stackdepth = -1; // stack depth at start
  string toString() {
    return Format("cpu(",
      (stackdepth != -1)?Format("@", stackdepth):"@?", " ",
      isValid?"[OK]":"[BAD]", " ", known,
      ", stack", noStack?"[none] ":" ", stack.length, "; ", stack,
      ", pop ", latepop, ", used ", use.keys, ", nvm ", nvmed,
    ")");
  }
  int getStackDelta() {
    return - stack.length * 4 + latepop.length * 4;
  }
  string mkIndirect(string val, int delta = 0 /* additional delta */) {
    if (val.startsWith("+(")) {
      auto op2 = val.between("(", ")"), op1 = op2.slice(",").strip();
      if (op1.startsWith("%gs:")) return null;
      op2 = op2.strip();
      if (op1.isRegister() && op2.isNumLiteral()) {
        auto op2i = op2.literalToInt();
        /*if (t.to in use)
          return null;*/
        // to indirect access
        auto sumdelt = op2i + delta;
        if (sumdelt) return qformat(sumdelt, "(", op1, ")");
        else return qformat("(", op1, ")");
      }
    }
    return null;
  }
  // does this super-instruction modify the stack?
  bool modsStack() {
    return stack.length || latepop.length;
  }
  bool update(Transaction t) {
    if (stackdepth == -1 && t.stackdepth != -1 && !modsStack()) {
      stackdepth = t.stackdepth;
    }
    accessParams(t, (ref string s) { s = s.cleanup(); });
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
      if (  s in known && known[  s] == whs) return true;
      foreach (entry; stack)
        if (entry.find(s) != -1) return false;
      foreach (key, value; known) {
        if (value.find(s) != -1) return false;
      }
      return true;
    }
    bool set(string mem, string val) {
      bool checkMode(string s) {
        if (s.find("%esp") != -1) {
          if (ebp_mode == -1) ebp_mode = false;
          else if (ebp_mode == true) return false;
        }
        if (s.find("%ebp") != -1) {
          if (ebp_mode == -1) ebp_mode = true;
          else if (ebp_mode == false) return false;
        }
        return true;
      }
      if (!checkMode(mem) || !checkMode(val)) return false;
      if (mem == val) known.remove(mem);
      else {
        if (val) { // if val is null, this is equivalent to void assignment. do nothing.
          if (mem.isRelative() && val.isRelative())
            return false;
          if (!(mem in known) && mem in use) // fallen out of use
            use.remove(mem);
          known[mem] = val;
        } else return false;
      }
      nvmed.remove(mem);
      return true;
    }
    if (t.kind != Transaction.Kind.Nevermind) {
      if (latepop && t.kind != Transaction.Kind.Pop)
                         return false;
    }
    // Note: this must NOT fix up the stack! think about it.
    void fixupESPDeps(int shift) {
      typeof(known) newknown;
      foreach (key, value; known) {
        fixupString(key, shift); fixupString(value, shift);
        newknown[key] = value;
      }
      known = newknown;
    }
    with (Transaction.Kind) switch (t.kind) {
      case Compare: return false;
      case LoadAddress:
        if (t.to.isRegister()) {
          if (t.to in use) break;
          int delta;
          if (auto reg = t.from.isIndirect2(delta)) {
            if (!set(t.to, qformat("+(", reg, ", $", delta, ")")))
              return false;
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
              if (!set(t.op2, qformat("+(",
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
            stack[$-1] = qformat("+(", mop1, ", $", mop2.literalToInt() + t.op1.literalToInt(), ")");
            mixin(Success);
          }
        }
        break;
      case SAlloc:
        if (t.size == 4) {
          stack ~= null;
          fixupESPDeps(4);
          mixin(Success);
        } else break;
      case SFree:
        if (t.size % nativePtrSize != 0) return false;
        auto st2 = stack;
        for (int i = 0; i < t.size / nativePtrSize; ++i)
          if (st2.length) st2 = st2[0 .. $-1];
          else return false;
        fixupESPDeps(-4 * (stack.length - st2.length));
        stack = st2;
        mixin(Success);
      case Mov:
        if (t.to == "%esp")
          return false;
        
        if (t.from == "%esp")
          return false; // TODO: can this ever be handled?
        if (t.from in known && known[t.from] == t.to) {
          // circular write, lol
          mixin(Success);
        }
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
            if (!stack.length) {
              if (latepop.length) break;
              auto mysrc = src;
              if (mysrc.isIndirect()) mysrc = t.from;
              if (!set(t.to, mysrc)) // t.from, not src, to prevent mem-to-mem movs
                return false;
              use[mysrc] = true;
              noStack = true;
              mixin(Success);
            }
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
          // TODO: handle this (stuff like '0(%eax, %ecx)')
          if (deref.find(",") != -1) return false;
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
              auto index = stack.length - 1 - from_rel;
              // can't just read stack - the stack address is understood to be only valid during stack building phase
              // auto val = stack[$ - 1 - from_rel];
              // instead "unroll" the stack until the index is _just_ at length, then set the value and uproll
              auto fixdist = 4 * (stack.length - index);
              auto src = stack[index];
              fixupString(src, fixdist);
              if (!set(t.to, src))
                return false;
              mixin(Success);
            } else {
              string src = cleanup(t.from);
              if (auto nsrc = src in known)
                src = *nsrc;
              if (!set(t.to, src))
                return false;
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
          int offs;
          auto indir = t.to.isIndirect2(offs);
          if (indir == "%esp" || (indir == "%ebp" && offs < 0))
            // access to live stack
            if (stack.length) return false;
            else noStack = true;
          if (!set(t.to, t.from))
            return false;
          mixin(Success);
        }
        break;
      case Label: return false;
      case Push:
        if (noStack)
          return false;
        if (t.type.size == nativePtrSize) {
          int offs;
          if (auto src = t.source.isIndirect2(offs)) {
            if (src in known) {
              if (auto indir = mkIndirect(known[src], offs)) {
                fixupESPDeps(4);
                if (indir.isIndirect() in known)
                  // depends on a register that we've yet to emit on stackbuild time
                  return false;
                
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
          // [edit] That's alright now, we can just update the ESP of knowns.
          // if (val in known) return false;
          if (auto reg = val.isIndirect2(offs)) {
            if (reg in known) return false; // bad dependence ordering
            // possible stack/variable dependence. bad.
            // TODO: only abort if we have outstanding stack writes
            if (reg == "%ebp" && offs < 0 && known.length)
              return false;
            use[reg] = true;
          }
          if (val.isRegister()) use[val] = true;
          // increment our knowns.
          fixupESPDeps(4);
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
          // do this first because pushed addresses were evaluated before the push took place
          fixupESPDeps(-4);
          if (!set(t.dest, stack[$-1])) {
            fixupESPDeps(4); // undo
            return false;
          }
          stack = stack[0 .. $-1];
          mixin(Success);
        }
        int offs;
        if (auto dest = t.dest.isIndirect2(offs)) {
          if (dest in known) {
            if (auto indir = mkIndirect(known[dest], offs)) {
              // if (!stack.length && latepop.length) break;
              if (stack.length) {
                auto newval = stack[$-1];
                if (newval.find("%esp") == -1 || (newval.find("%ebp") == -1 && offs < 0))
                  // not reliable to do push/pop stackwork before we move to the active stack
                  if (stack.length) return false;
                  else noStack = true;
                if (!set(indir, newval))
                  return false;
                // we have a pop! fix up the esp deps
                fixupESPDeps(-4);
                stack = stack[0 .. $-1];
                mixin(Success);
              } else {
                auto len = latepop.length;
                fixupESPDeps(-4 * len);
                latepop ~= mkIndirect(known[dest], offs); // re-eval indir for fixup
                fixupESPDeps(4 * len); // and undo
                mixin(Success);
              }
            }
          } else if (dest == "%esp") {
            if (stack.length && !isMemRef(stack[$-1])) {
              auto val = stack[$-1];
              fixupString(val, 4);
              if (!set(t.dest, val))
                return false;
              fixupESPDeps(-4);
              stack = stack[0 .. $-1];
              mixin(Success);
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
      case Call: return false;
      case Jump: return false;
      case FloatLoad, FloatIntLoad: return false;
      default: break;
    }
    return false;
    logln("---- Unsupported: ", t);
    logln("state ", this);
    assert(false);
  }
  bool isValid() {
    foreach (entry; stack) {
      if (auto rest = entry.startsWith("+(")) {
        return false;
      }
      if (!entry.strip().length) return false;
    }
    foreach (mem, value; known) {
      if (mem in nvmed) continue;
      if (!value) return false; // #INV
      if (auto rest = value.startsWith("+("))
        if (!mem.isRegister())
          return false;
        else
          continue;
      // TODO: move over eax or something
      if (mem.isRelative() && value.isRelative()) return false;
    }
    return true;
  }
  Transaction[] translate() {
    Transaction[] res;
    if (!isValid()) {
      res = knownGood ~ backup;
    } else {
      int myStackdepth; // local offs
      bool sd = stackdepth != -1;
      void addTransaction(Transaction.Kind tk,
        void delegate(ref Transaction) dg,
        void delegate(ref Transaction) dg2 = null
        ) {
        Transaction t;
        t.kind = tk;
        if (sd) t.stackdepth = stackdepth + myStackdepth;
        void fixup(ref string st) {
          int offs;
          /*if ("%esp" == st.isIndirect2(offs)) {
            // fix
            auto delta = offs + myStackdepth;
            if (delta)
              st = qformat(delta, "(%esp)");
            else
              st = "(%esp)";
          }*/
        }
        dg(t);
        accessParams(t, &fixup);
        if (dg2) dg2(t);
        
        res ~= t;
      }
      if (stack.length && noStack) {
        logln("Highly invalid processor state: ", this);
        asm { int 3; }
      }
      foreach (entry; stack) {
        addTransaction(Transaction.Kind.Push, (ref Transaction t) {
          t.source = entry;
          t.type = Single!(SysInt);
        }, (ref Transaction t) {
          myStackdepth += nativeIntSize;
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
        }, (ref Transaction t) {
          myStackdepth -= nativeIntSize;
        });
      }
      /*foreach (key, value; nvmed) {
        addTransaction(Transaction.Kind.Nevermind, (ref Transaction t) {
          t.dest = key;
        });
      }*/
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
        $SUBST(t);
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
      _changed = progress; // v secretly
      skip:; //   < < < < < < /
    } else {
      New(obj);
      t.obj = obj;
      if (obj.update($0)) { $SUBST(t, $1); }
      // else logln("Reject ", $0, ", ", $1);
    }
  `));
  // .ext_step = &ext_step; // export
  // opts = opts[0 .. $-1]; // only do ext_step once
  
  mixin(opt("rewrite_zero_ref", `*:
    info($0).hasOps
    =>
    auto t = $0;
    bool changed;
    accessParams(t, (ref string s) {
      if (s.startsWith("0(")) {
        s = s[1 .. $]; changed = true;
      }
    });
    if (changed) $SUBST(t);
  `));
  // alloc/free can be shuffled up past anything that doesn't reference stack.
  mixin(opt("sort_mem", `*, ^SAlloc || ^SFree:
    !referencesStack($0) && !affectsStack($0)
    =>
    int delta;
    if ($1.kind == $TK.SAlloc) delta = $1.size;
    else if ($1.kind == $TK.SFree) delta = -$1.size;
    else assert(false);
    auto t2 = $0;
    if (t2.hasStackdepth) t2.stackdepth += delta;
    $SUBST($1, t2);
  `));
  mixin(opt("sort_pointless_mem", `*, ^SAlloc || ^SFree:
    info($0).hasOps
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
        s = qformat(offs + shift, "(%esp)");
      } else {
        s = qformat(offs - shift, "(%esp)");
      }
    }
    accessParams(t, (ref string s) { detShift(s); });
    // ------------------------------
    accessParams(t, (ref string s) { applyShift(s); });
    bool substed;
    // override conas
    if ((
      !changesOrNeedsActiveStack($0) ||
      $0.kind == $TK.Mov /or/ $TK.FloatPop /or/ $TK.DoublePop /or/ $TK.FloatLoad /or/ $TK.FloatStore /or/ $TK.DoubleStore /or/ $TK.LoadAddress
    ) && (shift > 0 || shift == -1 && !dontDoIt)) {
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
      $SUBST(t2, t1);
  `));+/
  mixin(opt("collapse_alloc_frees", `^SAlloc || ^SFree, ^SAlloc || ^SFree =>
    int sum_inc;
    if ($0.kind == $TK.SAlloc) sum_inc += $0.size;
    else sum_inc -= $0.size;
    if ($1.kind == $TK.SAlloc) sum_inc += $1.size;
    else sum_inc -= $1.size;
    if (!sum_inc) $SUBST();
    else $SUBSTWITH {
      if (sum_inc > 0) kind = $TK.SAlloc;
      else kind = $TK.SFree;
      size = abs(sum_inc);
    }
  `));
  mixin(opt("cleanup_nop", `^SAlloc||^SFree: $0.size == 0
    => $SUBST();
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
    t2.source = qformat(offs + $0.op1.literalToInt(), "(", reg, ")");
    $SUBST(t2, t1);
  `));
  mixin(opt("scratch_mov", `^Mov, ^Call:
    $1.dest.isLiteral() && $0.to.isUtilityRegister()
    =>
    $SUBST($1);
  `));
  mixin(opt("fold_stores", `^FloatPop, ^Pop:
    $0.dest == "(%esp)" && $1.type.size == 4 && $1.dest != "(%esp)" /* lolwat? */
    =>
    $T t1 = $0.dup;
    t1.dest = $1.dest;
    $T t2;
    t2.kind = $TK.SFree;
    t2.size = 4;
    $SUBST(t1, t2);
  `));
  mixin(opt("fold_doublestores", `^DoublePop, ^Pop, ^Pop:
    $0.dest == "(%esp)" && $1.type.size == 4 && $2.type.size == 4
    && $1.dest == $2.dest && $1.dest != "(%esp)" /* lolwat? */
    =>
    $T t1 = $0.dup;
    t1.dest = $1.dest;
    $T t2;
    t2.kind = $TK.SFree;
    t2.size = 8;
    $SUBST(t1, t2);
  `));
  mixin(opt("sort_push_math", `^Push, ^MathOp:
    $0.source.isUtilityRegister() && $1.op2 == "(%esp)"
    =>
    $T t = $1.dup;
    t.op2 = $0.source;
    $SUBST(t, $0);
  `));
  mixin(opt("resolve_lea_free_load", `^LoadAddress, ^SFree, *:
    info($2).numInOps == 1 && info($2).opSize == 4 && info($2).inOp1().isIndirect(0) == $0.dest && $1.size == 4
    =>
    $T t = $2.dup;
    info(t).inOp1 = $0.from;
    $SUBST(t, $1);
  `));
  mixin(opt("merge_literal_adds", `^MathOp, ^MathOp:
    $0.opName == "addl" && $1.opName == "addl" &&
    $0.op1.isNumLiteral() && $1.op1.isNumLiteral() &&
    $0.op2 == "%eax" && $1.op2 == "%eax"
    =>
    $SUBSTWITH {
      kind = $TK.MathOp;
      opName = "addl";
      op1 = qformat("$", $0.op1.literalToInt() + $1.op1.literalToInt());
      op2 = "%eax";
    }
  `));
  mixin(opt("switch_mov_push", `^Mov, ^Push:
    $0.to.isUtilityRegister() && $0.to == $1.source && $1.type.size == nativePtrSize
    =>
    auto s0 = $1.dup(), s1 = $0.dup();
    s0.source = $0.from;
    s0.stackdepth = $1.stackdepth;
    s1.from = "(%esp)";
    s1.to = $0.to;
    $SUBST(s0, s1);
  `));
  //move movs upwards, lol
  /*mixin(opt("sort_mov", `*, ^Mov:
    $1.to.isUtilityRegister() && $1.from.isIndirect() == "%esp"
    && $0.kind != $TK.Mov
    && !affectsStack($0)
    =>
    bool problem;
    void check(string s) { if (s.find($1.to) != -1) problem = true; }
    accessParams($0, (ref string s) { check(s); });
    if (!problem) $SUBST($1, $0);
  `));*/
  /*mixin(opt("sort_floatload", `*, ^FloatLoad:
    !referencesStack($0) && !affectsStack($0) && $0.
    =>
    $SUBST($1, $0);
  `));*/
  mixin(opt("load_from_push", `^Push, (^FloatLoad/* || ^FloatIntLoad*/):
    !$0.source.isRegister() && $1.source == "(%esp)"
    =>
    $T a1 = $1.dup;
    a1.source = $0.source;
    if ($1.hasStackdepth) a1.stackdepth = $1.stackdepth - 4;
    $SUBST(a1, $0);
  `));
  mixin(opt("fold_float_pop_load", `^FloatPop, ^FloatLoad, ^SFree: $0.dest == $1.source && $0.dest == "(%esp)" && $2.size == 4 => $SUBST($2);`));
  mixin(opt("fold_double_pop_load", `^DoublePop, ^DoubleLoad, ^SFree: $0.dest == $1.source && $0.dest == "(%esp)" && $2.size == 8 => $SUBST($2);`));
  mixin(opt("fold_float_pop_load_to_store", `^FloatPop, ^FloatLoad: $0.dest == $1.source => $SUBSTWITH { kind = $TK.FloatStore; dest = $0.dest; }`));
  mixin(opt("fold_double_pop_load_to_store", `^DoublePop, ^DoubleLoad: $0.dest == $1.source => $SUBSTWITH { kind = $TK.DoubleStore; dest = $0.dest; }`));
  mixin(opt("make_call_direct", `^Mov, ^Call: $0.to == $1.dest => $SUBSTWITH { kind = $TK.Call; dest = $0.from; } `));
  
  mixin(opt("ebp_to_esp", `*:
    (
       getSrc($0).isIndirect() == "%ebp"
    || getDst($0).isIndirect() == "%ebp"
    )
    && $0.hasStackdepth && (!hasSize($0) || opSize($0) != 1)
    =>
    $T t = $0;
    bool changed;
    void doStuff(ref string str) {
      auto offs = str.between("", "(").atoi(); 
      auto new_offs = offs + t.stackdepth;
      if (new_offs) str = qformat(new_offs, "(%esp)");
      else str = "(%esp)";
      changed = true;
    }
    bool skip;
    if ($0.kind == $TK.Push /or/ $TK.Pop) {
      // if we can't do the push in one step
      if ($0.type.size != 4 /or/ 2 /or/ 1) 
        skip = true;
    }
    if (!skip) {
      accessParams(t, (ref string s) { if (s.isIndirect() == "%ebp") doStuff(s); });
      if (changed) $SUBST(t);
    }
  `));
  
  // jump opts
  mixin(opt("join_labels", `^Label, ^Label => auto t = $0; t.names ~= $1.names; t.keepRegisters |= $1.keepRegisters; $SUBST(t); `));
  mixin(opt("pointless_jump", `^Jump, ^Label:
    $1.hasLabel($0.dest)
    =>
    labels_refcount[$0.dest] --;
    $SUBST($1);
  `));
  mixin(opt("silly_mov", `^Mov, ^Mov:
    $0.to == $1.from && $1.to == $0.from
    &&
    $0.to.isRegister()
    =>
    $SUBST($0);
  `));
  mixin(opt("fold_float_load", `^LoadAddress, (^FloatLoad || ^FloatIntLoad || ^DoubleLoad || ^SSEOp):
    info($1).opIndirectMatch(0, $0.to)
    =>
    $T t = $1.dup;
    info(t).opIndirectMatchSet(0, $0.from);
    $SUBST(t);
  `));
  mixin(opt("fold_float_push_pop", `^DoublePop, (^FloatLoad || ^DoubleLoad), ^DoubleLoad:
    $0.dest == $2.source
    =>
    $T t1;
    t1.kind = $TK.DoubleStore;
    t1.dest = $0.dest;
    $T t2; t2.kind = $TK.FPSwap;
    $SUBST(t1, $1, t2);
  `));
  mixin(opt("float_pointless_swap", `^FPSwap, ^FloatMath:
    $1.opName == "fadd" || $1.opName == "fmul"
    =>
    $SUBST($1);
  `));
  mixin(opt("silly_push_2", `^Push, ^SFree:
    $0.type.size == 4 && $1.size > 4
    =>
    auto t = $1.dup;
    t.size -= 4;
    $SUBST(t);
  `));
  mixin(opt("sort_nevermind", `*, ^Nevermind:
    $0.kind != $TK.Nevermind
    =>
    bool refsMe;
    with ($TK)
      if ($0.kind == Label /or/ Jump /or/ Call /or/ SAlloc /or/ SFree)
        refsMe = true;
      else accessParams($0, (ref string s) { if (s.find($1.dest) != -1) refsMe = true; });
    if (!refsMe) {
      $SUBST($1, $0);
    }
  `));
  mixin(opt("combine_nevermind", `^Nevermind, ^Nevermind:
    $0.dest == $1.dest => $SUBST($0);
  `));
  mixin(opt("complex_pointless_store", `^FloatPop, ^SFree, ^FloatLoad, ^SFree:
    $1.size == 4 && $3.size == 4 &&
    $0.dest == "4(%esp)" && $2.source == "(%esp)"
    =>
    $SUBSTWITH {
      kind = $TK.SFree;
      stackdepth = $0.stackdepth;
      size = 8;
    }
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
        t.source = qformat(delta, "(", reg, ")");
        ts = t ~ ts;
        delta += 4;
      }
      $SUBST(ts);
    }
    if ($0.source.startsWith("%gs")) {
      int offs = $0.type.size;
      $T[] ts;
      int sd = $0.stackdepth;
      while (offs) {
        offs -= 4;
        $T t;
        t.kind = $TK.Push;
        t.type = Single!(SysInt);
        t.source = qformat(offs, "(", $0.source, ")");
        t.stackdepth = sd;
        sd += 4;
        ts ~= t;
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
        t.dest = qformat(delta, "(", reg, ")");
        ts ~= t;
        delta += 4;
      }
      $SUBST(ts);
    }
  `));
  mixin(opt("generic_waste", `*, ^SFree:
    getDstp($0) && opSize($0) == 4 && $1.size >= 4
    =>
    bool doit;
    if (getDst($0) == "(%esp)") doit = true;
    if ($0.kind == $TK.FloatPop) doit = false; // can't remove, has side effects
    if (doit) $SUBST($1); // pointless
  `));
  mixin(opt("direct_math", `^Mov, ^Mov, ^MathOp:
    $0.to == $2.op1 && $1.to == $2.op2 &&
    !collide($0.from, $1.to) && !collide($0.to, $1.from)
    =>
    $T t = $2;
    t.op1 = $0.from;
    $SUBST($1, t, $0);
  `));
  mixin(opt("direct_math_2", `^Mov, ^MathOp, ^Mov:
    $0.to.isUtilityRegister() && $0.to == $1.op2 &&
    $0.from == $2.to && $0.to == $2.from &&
    $1.op1.isNumLiteral() && $1.opName != "imull" /* :( */
    =>
    $T t1 = $1;
    t1.op2 = $0.from;
    $SUBST(t1, $0);
  `));
  mixin(opt("direct_int_load", `^Push, ^FloatIntLoad, ^SFree:
    $0.type.size == 4 && $1.source == "(%esp)" && $2.size == 4
    =>
    $T t = $1.dup;
    t.source = $0.source;
    $SUBST(t);
  `));
  mixin(opt("move_into_compare", `^Mov, ^Compare:
    $0.to.isUtilityRegister() && ($1.op2 == $0.to || $1.op1 == $0.to)
    /* wat */
    && !($0.from.isNumLiteral() && ($1.op1.isNumLiteral() || $1.op2.isNumLiteral()))
    // cmp can't handle two memory references at once.
    && !($1.op1 == $0.to && $1.op2.isMemRef() && $0.from.isMemRef())
    && !($1.op2 == $0.to && $1.op1.isMemRef() && $0.from.isMemRef())
    =>
    $T t = $1.dup;
    if (t.op1 == $0.to) t.op1 = $0.from;
    else                t.op2 = $0.from;
    $SUBST(t);
  `));
  // subl $num1, %reg, pushl num2(%reg), popl %reg => movl -num1+num2(%reg) -> %reg
  mixin(opt("fold_math_push", `^MathOp, ^Push, ^Pop:
    ($0.opName == "addl" || $0.opName == "subl") &&
    $0.op1.isNumLiteral() && $1.type.size == 4 &&
    $1.source.isIndirect() == $0.op2 &&
    $2.dest == $0.op2 && $2.type.size == 4
    =>
    $T t;
    t.kind = $TK.Mov;
    t.stackdepth = $0.stackdepth;
    
    int op1 = $0.op1.literalToInt();
    if ($0.opName == "subl") op1 = -op1;
    int op2;
    $1.source.isIndirect2(op2);
    
    t.from = qformat(op1 + op2, "(", $0.op2, ")");
    t.to = $0.op2;
    
    $SUBST(t);
  `));
  // subl $num1, mem, flds mem, nvm mem
  mixin(opt("fold_math_load_nvm", `^MathOp, ^FloatLoad, ^Nevermind:
    ($0.opName == "addl" || $0.opName == "subl") &&
    $0.op1.isNumLiteral() && $1.source.isIndirect() == $0.op2 &&
    $2.dest == $1.source
    =>
    $T t = $1;
    
    int op1 = $0.op1.literalToInt();
    if ($0.opName == "subl") op1 = -op1;
    int op2;
    $1.source.isIndirect2(op2);
    
    t.source = qformat(op1 + op2, "(", $0.op2, ")");
    $SUBST(t);
  `));
  mixin(opt("remove_redundant_mov", `^Mov, ^FloatLoad, ^Mov, ^FloatLoad:
    $0.from == $2.from && $0.to == $2.to
    =>
    $T t;
    // good luck working out why ~
    t.kind = $TK.FPSwap;
    $SUBST($0, $1, $3);
  `));
  // push %reg1, mov x -> %reg1, pop %reg2 => mov %reg1 -> %reg2, mov x -> %reg1
  mixin(opt("fold_push_mov_pop", `^Push, ^Mov, ^Pop:
    $0.type.size == 4 && $2.type.size == 4 &&
    $0.source.isRegister() &&
    $0.source == $1.to && $1.from.find($2.dest) == -1 /* to be sure */
    && !referencesStack($1)
    =>
    $T t1;
    t1.stackdepth = $0.stackdepth;
    t1.kind = $TK.Mov;
    t1.from = $0.source;
    t1.to = $2.dest;
    
    $T t2 = $1;
    t2.stackdepth = t1.stackdepth;
    
    $SUBST(t1, t2);
  `));
  mixin(opt("reorder_math_mov", `^MathOp, ^Mov, ^Mov:
    $0.op1.isLiteral() && $0.op2.isRegister() &&
    $0.op2 == $1.from && $1.to.isRegister() &&
    $2.from.isLiteral() && $2.to == $1.from
    =>
    $T t1 = $1, t2 = $0;
    t2.op2 = t1.to;
    $SUBST(t1, t2, $2);
  `));
  mixin(opt("reorder_math_mov_math", `^MathOp, ^Mov, ^MathOp:
    $0.op1.isLiteral() && $2.op1.isLiteral() &&
    $0.op2.isRegister() && $2.op2.isRegister() &&
    $0.op2 == $1.from && $1.to == $2.op2
    =>
    $T t1 = $1, t2 = $0, t3 = $1;
    t2.op2 = t1.to;
    t3.from = t1.to; t3.to = t1.from;
    $SUBST(t1, t2, t3, $2);
  `));
  mixin(opt("reorder_mov_math", `^Mov, ^MathOp:
    $0.from.isRegister() && $0.to.isRegister() &&
    $1.op1 == $0.to && $1.op2.isRegister() &&
    $1.op2 != $0.from
    =>
    $T t = $1;
    t.op1 = $0.from;
    $SUBST(t, $0);
  `));
  mixin(opt("hyperspecific", `^Label, ^Push, ^Push, ^Push, ^Pop, ^Pop, ^Pop
    =>
    $T ts[6];
    foreach (ref t; ts) t.kind = $TK.Mov;
    ts[0].from = $1.source; ts[0].to = "%eax";
    ts[1].from = $2.source; ts[1].to = "%ebx";  fixupString(ts[1].from, -4);
    ts[2].from = $3.source; ts[2].to = "%ecx";  fixupString(ts[2].from, -8);
    ts[3].from = "%eax";    ts[3].to = $6.dest; fixupString(ts[3].to, -4);
    ts[4].from = "%ebx";    ts[4].to = $5.dest; fixupString(ts[4].to, -8);
    ts[5].from = "%ecx";    ts[5].to = $4.dest; fixupString(ts[5].to, -12);
    $SUBST($0, ts);
  `));
  mixin(opt("move_sooner", `^MathOp, ^Mov, *:
    $0.op1.find($0.op2) == -1 && $0.op1.find($1.to) == -1 &&
    (!$0.op1.isIndirect() || !$1.to.isIndirect()) &&
    $1.from == $0.op2 && $1.to.isUtilityRegister() &&
    getDst($2) == $0.op2
    =>
    $T t = $0;
    t.op2 = $1.to;
    $SUBST($1, t, $2);
  `));
  mixin(opt("float_load_twice", `^FloatLoad, ^FloatLoad:
    $0.source == $1.source
    =>
    $T t = $1;
    t.kind = $TK.RegLoad;
    t.source = "%st";
    $SUBST($0, t);
  `));
  mixin(opt("float_compare_direct", `^Push, ^FloatCompare, ^SFree:
    $0.type.size == 4 && $1.source == "(%esp)" && $2.size == 4
    =>
    $T t = $1;
    t.source = $0.source;
    $SUBST(t);
  `));
  /*mixin(opt("push_salloc_smoother", `^Push, ^SAlloc:
    $0.type.size == 4 && $1.size && !$0.source.isRelative()
    =>
    $T t1 = $1.dup;
    t1.size += 4;
    $T t2;
    t2.kind = $TK.Mov;
    t2.from = $0.source;
    fixupString(t2.from, 4 + $1.size);
    t2.to = qformat($1.size, "(%esp)");
    $SUBST(t1, t2);
  `));*/
  mixin(opt("ext_mem_form", `^MathOp, ^Push, ^Pop:
    $0.opName == "addl" &&
    $0.op1.isUtilityRegister() && $0.op2.isUtilityRegister() &&
    $1.source.isIndirect(0) == $0.op2 &&
    $2.dest == $0.op2
    =>
    $T t;
    t.kind = $TK.Mov;
    assert($1.type.size == $2.type.size);
    t.from = qformat("(", $0.op2, ",", $0.op1, ")");
    t.to = $2.dest;
    $SUBST(t);
  `));
  mixin(opt("a_bug_somewhere", `^Mov, ^Mov, ^Mov:
    $0.to.isUtilityRegister() &&
    $0.to == $1.from && $1.to.isUtilityRegister() &&
    $2.to == $0.to
    =>
    $T t = $0;
    t.to = $1.to;
    $SUBST(t, $2);
  `));
  mixin(opt("math_ref_merge", `^MathOp, *:
    $0.op1.isNumLiteral() && $0.op2.isUtilityRegister() &&
    ($0.opName == "addl" || $0.opName == "subl") &&
    getSrc($1).isIndirect() == $0.op2
    =>
    $T t = $1;
    string mem = qformat("(", $0.op2, ")");
    int offset;
    getSrc(t).isIndirect2(offset);
    if ($0.opName == "addl") mem = qformat(offset + $0.op1.literalToInt(), mem);
    else mem = qformat(offset - $0.op1.literalToInt(), mem);
    *getSrcp(t) = mem;
    $SUBST(t, $0);
  `));
  mixin(opt("move_lea_down", `^LoadAddress, *:
    $1.kind != $TK.LoadAddress &&
    (!getSrc($1) || getSrc($1).find($0.to) == -1) &&
    (!getDst($1) || getDst($1).find($0.to) == -1)
    =>
    $SUBST($1, $0);
  `));
  bool lookahead_remove_redundants(Transcache cache, ref int[string] labels_refcount) {
    bool changed, pushMode;
    auto match = cache.findMatch("lookahead_remove_redundants", delegate int(Transaction[] list) {
      if (list.length <= 1) return false;
      auto head = list[0];
      string check;
      with (Transaction.Kind) {
        if (head.kind == Mov || head.kind == LoadAddress) check = head.to;
        if (head.kind == FloatStore ) check = head.dest;
        if (head.kind == DoubleStore) check = head.dest;
        if (head.kind == MathOp) check = head.op2;
        pushMode = false;
        if (head.kind == Push && head.type.size == 4) { pushMode = true; check = "(%esp)"; }
      }
      
      if (!check) return false;
      if (!check.isUtilityRegister() && check != "(%esp)") return false;
      
      bool hasStackDependence(string s) {
        if (s.find("%esp") != -1) return true;
        int offs;
        if (s.isIndirect2(offs) == "%ebp") return offs < 0;
        return false;
      }
      
      bool unneeded;
      int i;
      bool test(string s) {
        if (s.find(check) != -1) return true;
        if (check == "(%esp)" && hasStackDependence(s)) return true;
        return false;
      }
      outer:foreach (_i, entry; list[1 .. $]) {
        i = _i;
        with (Transaction.Kind) switch (entry.kind) {
          case SFree: if (check == "(%esp)") { unneeded = true; break outer; }
          case SAlloc: if (check == "(%esp)") break outer;
          case FloatMath:
            continue;    // no change
          
          case Jump:
            if (entry.keepRegisters) break outer;
          case Call:
            if (check.isUtilityRegister()) {
              // arguments on the stack (cdecl)
              if (!test(entry.dest))
                unneeded = true;
              break outer;
            }
          case Label:
            if (entry.keepRegisters) break outer;
            if (check != "(%esp)") unneeded = true;
          case Compare:
            break outer;
          
          case ExtendDivide:
            if (check == "%eax") break outer;
          case Push:
            if (check == "(%esp)") break outer;
          case FloatLoad, DoubleLoad, RealLoad, RegLoad, FloatIntLoad, FloatCompare:
            if (test(entry.source)) break outer;
            continue;
          
          case Pop:
            if (check == "(%esp)") break outer;
          case Nevermind, FloatPop, DoublePop, FloatStore, DoubleStore:
            if (entry.dest == check) { unneeded = true; break outer; }
            if (test(entry.dest)) break outer;
            continue;
          
          case MathOp:
            if (test(entry.op1) || test(entry.op2)) break outer;
            continue;
          
          case Mov, LoadAddress:
            if (test(entry.from)) break outer;
            if (entry.to == check) {
              unneeded = true;
              break outer;
            }
            if (test(entry.to)) break outer;
            continue;
          
          case SSEOp:
            if (test(entry.op1)) break outer;
            if (entry.op2 == check) { // all SSE ops have the target as the second operand
              unneeded = true;
              break outer;
            }
            if (test(entry.op2)) break outer;
            continue;
          
          default: break;
        }
        logln("huh? ", entry);
        assert(false);
      }
      if (unneeded) return i + 2;
      return false;
    });
    if (match.length) do {
      if (pushMode) {
        Transaction t;
        t.kind = Transaction.Kind.SAlloc;
        t.size = 4;
        match.replaceWith(t, match[][1 .. $]);
      } else {
        match.replaceWith(match[][1 .. $]); // remove
      }
      changed = true;
    } while (match.advance());
    return changed;
  }
  opts ~= stuple(&lookahead_remove_redundants, "lookahead_remove_redundants", true);
  
  bool lookahead_bridge_push_pop(Transcache cache, ref int[string] labels_refcount) {
    bool changed;
    Transaction[] repl;
    // BEWARE!
    // this opt is iffy. it does not guarantee that its scratch registers are actually available!
    auto match = cache.findMatch("lookahead_bridge_push_pop", delegate int(Transaction[] list) {
      with (Transaction.Kind) {
        if (list.length <= 2) return false;
        auto head = list[0];
        if (head.kind != Push || head.type.size != 4) return false;
        if (!head.source.isUtilityRegister() && !head.source.isIndirect().isUtilityRegister()
            && !head.source.isNumLiteral()
            && head.source.isIndirect() != "%esp") return false;
        
        int tailid = -1;
        for (int i = 0; i < list.length; ++i) {
          if (list[i].kind == Pop || list[i].kind == SFree) { tailid = i; break; }
        }
        if (tailid == -1) return false;
        auto tail = list[tailid];
        if (tail.kind == Pop) {
          if (tail.type.size != 4) return false;
          if (!tail.dest.isUtilityRegister()/* && !tail.dest.isIndirect().isUtilityRegister()*/) return false;
        } else {
          if (tail.size != 4) return false;
        }
        
        auto segment = list[0 .. tailid + 1];
        if (segment.length <= 2) return false;
        segment = segment.dup;
        // if (head.source.isNumLiteral()) logln("Try to bridge ", segment);
        
        foreach (entry; segment[1 .. $-1]) {
          if (entry.kind == Push /or/ Call /or/ Label /or/ Nevermind)
            return false;
          if (affectsStack(entry))
            return false;
        }
        
        bool[string] unused;
        foreach (reg; ["%edx", "%ecx"/*, "%ebx", "%eax"*/])
          unused[reg] = true;
        foreach (ref entry; segment[1 .. $-1]) {
          bool oops; // oops, can't do it.
          accessParams(entry, (ref string s) {
            string[] remove;
            foreach (key, value; unused)
              if (s.find(key) != -1) remove ~= key;
            foreach (entry; remove) unused.remove(entry);
            if (s == "(%esp)") { oops = true; return; }
            fixupString(s, -4);
          });
          if (oops) return false;
          if (entry.hasStackdepth()) entry.stackdepth -= 4;
        }
        
        if (tail.kind == SFree) {
          repl = segment[1 .. $-1];
          return segment.length;
        }
        if (!unused.length) return false;
        if (head.source.isRegister() && head.source in unused) {
          segment[$-1] = Init!(Transaction);
          with (segment[$-1]) {
            kind = Mov;
            from = head.source;
            to = tail.dest;
          }
          repl = segment[1 .. $];
          return segment.length;
        }
        
        if (tail.dest.isRegister() && tail.dest in unused) {
          segment[0] = Init!(Transaction);
          with (segment[0]) {
            kind = Mov;
            from = head.source;
            to = tail.dest;
          }
          repl = segment[0 .. $-1];
          return segment.length;
        }
        
        if (head.source.isRegister() && head.source == tail.dest) {
          auto subst = unused.keys[0];
          foreach (ref entry; segment[1 .. $-1]) {
            accessParams(entry, (ref string s) {
              s = s.replace(head.source, subst);
            });
          }
          repl = segment[1 .. $-1];
          return segment.length;
        }
        
        auto subst = unused.keys[0];
        segment[0] = Init!(Transaction);
        with (segment[0]) {
          kind = Mov;
          from = head.source;
          to = subst;
        }
        segment[$-1] = Init!(Transaction);
        with (segment[$-1]) {
          kind = Mov;
          from = subst;
          to = tail.dest;
        }
        repl = segment;
        return segment.length;
      }
      return false;
    });
    if (match.length) do {
      match.replaceWith(repl);
      changed = true;
    } while (match.advance());
    return changed;
  }
  opts ~= stuple(&lookahead_bridge_push_pop, "lookahead_bridge_push_pop", true);
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
