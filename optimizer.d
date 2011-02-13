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

// returns null if s points at SSE reg
string* doSSE(string* s, bool isOp2 = false, string opName = null) {
  if ((*s).startsWith("%xmm")) return null;
  // these don't read from op2
  if (isOp2 && opName == "movaps" /or/ "movups") return null;
  return s;
}

struct TransactionInfo {
  Transaction* tp;
  /*
    info on Nevermind: even though it doesn't actually write to its
      output operand, we want the optimizer to treat it like it does.
    TODO: is MathOp always 4-sized?
  */
  const string Table = `
    name       | inOp1     | inOp2  | outOp |size |stack
    -----------------------------------------------------
    Push       | &#.source |        |       | #.type.size| grow
    Pop        |           |        |&#.dest| #.type.size|shrink
    SAlloc     |           |        |       | #.size | grow
    SFree      |           |        |       | #.size |shrink
    Label      |           |        |       | -1  |
    Jump       | &#.dest   |        |       | -1  |
    Call       | &#.dest   |        |       | -1  |
    Nevermind  |           |        |&#.dest| -1  |
    MathOp     | &#.op1    | &#.op2 | &#.op2|  4  |
    ExtendDivide|&#.source |        |       |  4  |
    Compare    |&#.op1     | &#.op2 |       |  4  |
    LoadAddress|&#.from    |        | &#.to |  4  |
    Mov        | &#.from   |        | &#.to |  4  |
    Mov2       | &#.from   |        | &#.to |  2  |
    Mov1       | &#.from   |        | &#.to |  1  |
    FloatLoad  | &#.source |        |       |  4  |
    DoubleLoad | &#.source |        |       |  8  |
    RealLoad   | &#.source |        |       | 10  |
    FloatIntLoad|&#.source |        |       |  4  |
    FloatCompare|&#.source |        |       |  4  |
    FloatPop   |           |        |&#.dest|  4  |
    FloatStore |           |        |&#.dest|  4  |
    DoublePop  |           |        |&#.dest|  8  |
    DoubleStore|           |        |&#.dest|  8  |
    FloatMath  |           |        |       | -1  |
    FPSwap     |           |        |       | -1  |
    RegLoad    |           |        |       | -1  |
    SSEOp      |doSSE(&#.op1)|doSSE(&#.op2,true,#.opName)|doSSE(&#.op2)| 16  |
  `;
  template TableOp(string Body, R, T...) {
    R TableOp(T t) {
      mixin(
        `switch (tp.kind) {
        ` ~ Table.ctTableUnroll(`case Transaction.Kind.$name:
          ` ~ Body) ~ `
          default: break;
        }`);
      logln("but what about ", *tp);
      asm { int 3; }
    }
  }
  int numInOps() {
    int res;
    if (inOp1()) res ++;
    if (inOp2()) res ++;
    return res;
  }
  template inOp(string Name) {
    alias TableOp!(`
      static if ("$`~Name~`" == "") return null;
      else {
        auto ptr = mixin("$`~Name~`".ctReplace("#", "(*tp)"));
        if (!ptr) return null;
        return *ptr;
      }
    `, string) inOpRead;
    alias TableOp!(`
      static if ("$`~Name~`" == "") {
        logln("No op2 for ", *tp);
        asm { int 3; }
      } else {
        return mixin("*$`~Name~` = t[0]".ctReplace("#", "(*tp)"));
      }
    `, string, string) inOpWrite;
  }
  string inOp1() { return inOp!("inOp1").inOpRead(); }
  string inOp2() { return inOp!("inOp2").inOpRead(); }
  string inOp1(string s) { return inOp!("inOp1").inOpWrite(s); }
  string inOp2(string s) { return inOp!("inOp2").inOpWrite(s); }
  alias TableOp!(`return "$stack" == "grow";`, bool) growsStack;
  alias TableOp!(`return "$stack" == "shrink";`, bool) shrinksStack;
  bool resizesStack() { return growsStack() || shrinksStack(); }
  alias TableOp!(`return mixin("$size".ctReplace("#", "(*tp)")); `, int) opSize;
  alias TableOp!(`
    static if ("$outOp" == "") return null;
    else {
      auto ptr = mixin("$outOp".ctReplace("#", "(*tp)"));
      if (!ptr) return null;
      return *ptr;
    }
  `, string) outOp;
  alias TableOp!(`
    static if ("$outOp" == "") {
      logln("Can't set out op for ", tp.kind, ": invalid");
      asm { int 3; }
    } else return mixin("*$outOp = t[0]".ctReplace("#", "(*tp)"));
  `, string, string) outOp;
  bool hasOps() {
    return numInOps || outOp;
  }
  bool hasIndirectSrc(string s) {
    return
      (inOp1().isIndirect() == s)
    ||(inOp2().isIndirect() == s);
  }
  bool hasIndirect(string s) {
    return hasIndirectSrc(s) || outOp().isIndirect() == s;
  }
  string getIndirectSrc(string s) {
    if (inOp1().isIndirect() == s) return inOp1();
    if (inOp2().isIndirect() == s) return inOp2();
    asm { int 3; }
  }
  void setIndirectSrc(string s, string t) {
    if (inOp1().isIndirect() == s) inOp1 = t;
    else if (inOp2().isIndirect() == s) inOp2 = t;
    else asm { int 3; }
  }
  bool hasIndirectSrc(int i, string s) {
    return
      (inOp1().isIndirect(i) == s)
    ||(inOp2().isIndirect(i) == s);
  }
  bool hasIndirect(int i, string s) {
    return hasIndirectSrc(i, s)
    ||(outOp().isIndirect(i) == s);
  }
  void setIndirectSrc(int i, string s, string r) {
    if (inOp1().isIndirect(i) == s) inOp1 = r;
    if (inOp2().isIndirect(i) == s) inOp2 = r;
  }
  void setIndirect(int i, string s, string r) {
    setIndirectSrc(i, s, r);
    if (outOp().isIndirect(i) == s) outOp = r;
  }
  bool opContains(string s) {
    if (!s) return false;
    return
      inOp1().find(s) != -1
    ||inOp2().find(s) != -1
    ||outOp().find(s) != -1;
  }
  static bool couldFixup(string s, int by) {
    int offs;
    if (s.isIndirect2(offs) != "%esp") return true; // false -> * == true
    return offs >= -by;
  }
  bool couldFixup(int shift) {
    return couldFixup(inOp1(), shift) && couldFixup(inOp2(), shift) && couldFixup(outOp(), shift);
  }
  void fixupStrings(int shift) {
    auto s1 = inOp1(), s2 = inOp2(), s3 = outOp();
    s1.fixupString(shift); s2.fixupString(shift); s3.fixupString(shift);
    if (inOp1()) inOp1 = s1;
    if (inOp2()) inOp2 = s2;
    if (outOp()) outOp = s3;
  }
  void accessParams(void delegate(ref string) dg, bool writeonly = false) {
    auto s1 = inOp1(), s2 = inOp2(), s3 = outOp();
    if (s1 && !writeonly) { dg(s1); inOp1 = s1; }
    if (s2 && !writeonly) { dg(s2); inOp2 = s2; }
    if (s3) { dg(s3); outOp = s3; }
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
  if (affects) info(t).accessParams(&test, true);
  else         info(t).accessParams(&test);
  return res;
}

bool affectsStack(ref Transaction t) { return referencesStack(t, true); }

bool changesOrNeedsActiveStack(ref Transaction t) {
  return referencesStack(t, false, true) || referencesStack(t, true, true);
}

bool willOverwrite(ref Transaction t, string what) {
  if (!what.isRegister()) return false;
  bool res;
  info(t).accessParams((ref string s) { res |= s == what; }, true);
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
  info(t).accessParams(delegate void(ref string s) {
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
    info(t).accessParams((ref string s) { s = s.cleanup(); });
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
    asm { int 3; }
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
        info(t).accessParams(&fixup);
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
    info(t).accessParams((ref string s) {
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
        if (s.isIndirect().isUtilityRegister()) dontDoIt = true; // might still point at the stack.
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
    // if (t.kind == $TK.SSEOp) logln("test ", t);
    info(t).accessParams((ref string s) { detShift(s); });
    // ------------------------------
    info(t).accessParams((ref string s) { applyShift(s); });
    // if (t.kind == $TK.SSEOp) logln("blocked? ", dontDoIt);
    bool substed;
    // override conas
    if ((
      !changesOrNeedsActiveStack($0) ||
      $0.kind == $TK.Mov /or/ $TK.FloatPop /or/ $TK.DoublePop /or/ $TK.FloatLoad
      /or/ $TK.FloatStore /or/ $TK.DoubleStore /or/ $TK.LoadAddress /or/ $TK.SSEOp
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
  mixin(opt("make_call_direct", `^Mov, ^Call: $0.to == $1.dest => $SUBSTWITH { kind = $TK.Call; dest = $0.from; } `));
  
  mixin(opt("ebp_to_esp", `*:
    info($0).hasIndirect("%ebp")
    && $0.hasStackdepth && info($0).opSize != 1
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
      info(t).accessParams((ref string s) { if (s.isIndirect() == "%ebp") doStuff(s); });
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
  mixin(opt("move_lea_down", `^LoadAddress, *:
    $1.kind != $TK.LoadAddress &&
    !info($1).opContains($0.to)
    =>
    $T t = $0.dup;
    bool remove;
    auto size1 = info($1).opSize;
    auto it = info(t);
    if (info($1).growsStack) it.fixupStrings( size1);
    if (info($1).shrinksStack) {
      if (it.couldFixup(-size1))
        it.fixupStrings(-size1);
      else
        remove = true;
    }
    if (remove) $SUBST($1); // stack change makes lea invalid.
    else $SUBST($1, t);
  `));
  mixin(opt("move_lea_downer", `^LoadAddress, ^SFree, *:
    $2.kind != $TK.LoadAddress &&
    !info($2).opContains($0.to) && !info($2).resizesStack()
    =>
    $T t = $2.dup;
    info(t).fixupStrings($1.size);
    $SUBST(t, $0, $1);
  `));
  mixin(opt("load_address_into_source", `^LoadAddress, *:
    info($1).hasIndirect(0, $0.to) && info($1).opSize() > 1
    =>
    $T t = $1.dup;
    info(t).setIndirect(0, $0.to, $0.from);
    $T t2 = $0.dup;
    if (info($1).growsStack)   info(t2).fixupStrings( info($1).opSize());
    if (info($1).shrinksStack) info(t2).fixupStrings(-info($1).opSize());
    $SUBST(t, t2);
  `));
  // moved the sfree up too far!
  mixin(opt("load_address_into_sourcer", `^LoadAddress, ^SFree, *:
    info($2).hasIndirect(0, $0.to) && info($2).opSize() > 1
    =>
    $T t = $2.dup;
    info(t).setIndirect(0, $0.to, $0.from);
    $T t2 = $0.dup;
    if (info($2).growsStack)   info(t2).fixupStrings( info($2).opSize());
    if (info($2).shrinksStack) info(t2).fixupStrings(-info($2).opSize());
    $SUBST(t, t2, $1);
  `));
  mixin(opt("store_into_pop", `*, ^Pop:
    info($0).numInOps() == 0 && info($0).outOp().isIndirect(0) == "%esp" && info($0).opSize == $1.type.size
    =>
    $T t1;
    t1.kind = $TK.SFree;
    t1.size = info($0).opSize;
    $T t2 = $0.dup;
    // don't need to fix up t's sources; no op can freely both read and write from memory
    // do need to fix up dest though
    auto dest = $1.dest;
    dest.fixupString(-t1.size);
    info(t2).outOp = dest;
    $SUBST(t1, t2);
  `));
  // FP small fry
  mixin(opt("float_fold_redundant_save_load", `^FloatPop || ^DoublePop, ^FloatLoad || ^DoubleLoad:
    $0.dest == $1.source && info($0).opSize == info($1).opSize
    =>
    $T t;
    if ($0.kind == $TK.FloatPop) t.kind = $TK.FloatStore;
    else t.kind = $TK.DoubleStore;
    t.dest = $0.dest;
    $SUBST(t);
  `));
  mixin(opt("push_temp_into_load", `^Push, *:
    $0.type.size == info($1).opSize &&
    info($1).hasIndirectSrc(0, "%esp") &&
   !info($1).resizesStack() &&
    info($1).outOp().isIndirect() != "%esp" &&
   !info($0).opContains(info($1).outOp()) &&
    $1.kind != $TK.FloatIntLoad /* can't do mem loads :( */ &&
    $1.kind != $TK.LoadAddress /* lel */
    =>
    $T t = $1.dup;
    info(t).setIndirectSrc(0, "%esp", $0.source);
    $SUBST(t, $0);
  `));
  mixin(opt("pop_into_far_load", `^FloatPop, ^FloatLoad, ^FloatLoad:
    $0.dest == $2.source
    =>
    $T t = $0.dup;
    t.kind = $TK.FloatStore;
    $T t2;
    t2.kind = $TK.FPSwap;
    $SUBST(t, $1, t2);
  `));
  // nvm opts
  mixin(opt("nevermind_up", `*, ^Nevermind:
    $0.kind != $TK.Nevermind && !info($0).opContains($1.dest) &&
    $0.kind != $TK.SAlloc /or/ $TK.SFree /or/ $TK.Label /or/ $TK.Jump /or/ $TK.Call
    =>
    $SUBST($1, $0);
  `));
  mixin(opt("matching_nvms", `^Nevermind, ^Nevermind:
    $0.dest == $1.dest => $SUBST($0);
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
        asm { int 3; }
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
          info(entry).accessParams((ref string s) {
            string[] remove;
            foreach (key, value; unused)
              if (s.find(key) != -1) remove ~= key;
            foreach (entry; remove) unused.remove(entry);
            if (s.isIndirect(0) == "%esp") { oops = true; return; }
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
            info(entry).accessParams((ref string s) {
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
