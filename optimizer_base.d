module optimizer_base;

import tools.ctfe, tools.base, ast.base;
import assemble;
alias asmfile.startsWith startsWith;
alias tools.base.Stuple Stuple;

int xpar = -1; // for debugging

// dg, name, allow, barrier
Stuple!(bool delegate(Transcache, ref int[string]), string, bool, bool)[] opts;

// return false on failure
// note: not applicable is not a failure!
bool tryFixupString(ref string s, int shift) {
  if (isARM) {
    logln("TODO/ARM: fixup ", s, " by ", shift);
    return false;
  }
  if (auto rest = s.startsWith("+(%esp,")) {
    auto op2 = s.between("(", ")"), op1 = op2.rslice(",").strip();
    op2 = op2.strip().startsWith("$");
    assert(op2);
    auto sum = op2.my_atoi() + shift;
    if (sum < 0) return false;
    s = qformat("+("[], op1, ", $"[], sum, ")"[]);
    return true;
  }
  int offs;
  if (s.isIndirect2(offs).contains("%esp")) {
    if (offs + shift < 0) { // never a good idea
      return false;
    }
    s = qformat(offs + shift, "("[], s.isIndirect2(offs), ")"[]).cleanup();
  }
  return true;
}

void fixupString(ref string s, int shift) {
  if (!tryFixupString(s, shift)) {
    logln("Tried to fix up ", s, " by ", shift, " into negative! ");
    fail;
  }
}

// returns null if s points at SSE reg
string* doSSE(string* s, bool isOp2 = false, string opName = null) {
  // if ((*s).startsWith("%xmm")) return null;
  // these don't read from op2
  if (isOp2 && opName == "movaps"[] /or/ "movups"[]) return null;
  return s;
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
    Push       | &#.source |        |       | #.size| grow
    Pop        |           |        |&#.dest| #.size|shrink
    SAlloc     |           |        |       | #.size| grow
    SFree      |           |        |       | #.size|shrink
    Label      |           |        |       | -1  |
    Jump       | &#.dest   |        |       | -1  |
    Call       | &#.dest   |        |       | -1  |
    Nevermind  |           |        |&#.dest| -1  |
    MathOp     | &#.op1    | &#.op2 | &#.op2|  4  |
    ExtendDivide|&#.source |        |       |  4  |
    Compare    |&#.op1     | &#.op2 |       |  4  |
    LoadAddress|&#.from    |        | &#.to |  4  |
    MovD       | &#.from   |        | &#.to |  4  |
    Mov        | &#.from   |        | &#.to |  4  |
    Mov2       | &#.from   |        | &#.to |  2  |
    Mov1       | &#.from   |        | &#.to |  1  |
    FloatLoad  | &#.source |        |       |  4  |
    DoubleLoad | &#.source |        |       |  8  |
    RealLoad   | &#.source |        |       | 10  |
    FloatLongLoad|&#.source|        |       |  8  |
    FloatIntLoad|&#.source |        |       |  4  |
    FloatCompare|&#.source |        |       |  4  |
    FloatPop   |           |        |&#.dest|  4  |
    FloatStore |           |        |&#.dest|  4  |
    DoublePop  |           |        |&#.dest|  8  |
    DoubleStore|           |        |&#.dest|  8  |
    FPIntPop   |           |        |&#.dest|  4  |
    FPLongPop  |           |        |&#.dest|  8  |
    FloatMath  | &#.op1    |        |       | -1  |
    PureFloat  |           |        |       | -1  |
    Swap       | &#.source |&#.dest |&#.dest| -1  |
    RegLoad    |           |        |       | -1  |
    SSEOp      |doSSE(&#.op1)|doSSE(&#.op2,true,#.opName)|doSSE(&#.op2)| 16  |
    Text       |           |        |       | -1  |
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
      fail;
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
        fail;
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
  int stackchange() { if (growsStack) return opSize(); else if (shrinksStack) return -opSize(); else return 0; }
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
      fail;
    } else return mixin("*$outOp = t[0]".ctReplace("#", "(*tp)"));
  `, string, string) outOp;
  bool hasOps() {
    return numInOps || outOp;
  }
  bool hasIndirectSrc(string s) {
    return
      (inOp1().isIndirect().contains(s))
    ||(inOp2().isIndirect().contains(s));
  }
  bool hasIndirect(string s) {
    return hasIndirectSrc(s) || outOp().isIndirect().contains(s);
  }
  bool hasIndirectSrcEq(string s) {
    return
      (inOp1().isIndirect() == s)
    ||(inOp2().isIndirect() == s);
  }
  bool hasIndirectEq(string s) {
    return hasIndirectSrcEq(s) || outOp().isIndirect() == s;
  }
  string getIndirectSrc(string s) {
    if (inOp1().isIndirect().contains(s)) return inOp1();
    if (inOp2().isIndirect().contains(s)) return inOp2();
    fail;
  }
  void setIndirectSrc(string s, string t) {
    if (inOp1().isIndirect().contains(s)) inOp1 = t;
    else if (inOp2().isIndirect().contains(s)) inOp2 = t;
    else fail;
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
  bool opEqual(string s) {
    if (!s) return false;
    return
      inOp1() == s
    ||inOp2() == s
    ||outOp() == s;
  }
  bool sseContains(string s) {
    if (tp.kind != Transaction.Kind.SSEOp)
      fail;
    return tp.op1.find(s) != -1
        || tp.op2.find(s) != -1;
  }
  bool opContainsSrc(string s) {
    if (!s) return false;
    if (s == "%ax" && opContainsSrc("%eax")) return true;
    return
      inOp1().find(s) != -1
    ||inOp2().find(s) != -1;
  }
  bool opContains(string s) {
    if (!s) return false;
    if (s == "%ax" && opContains("%eax")) return true;
    return
      opContainsSrc(s)
    ||outOp().find(s) != -1;
  }
  static bool couldFixup(string s, int by) {
    int offs;
    if (!s.isIndirect2(offs).contains("%esp")) return true;
    return offs >= -by;
  }
  bool couldFixup(int shift) {
    with (Transaction.Kind)
      if (tp.kind != SSEOp /or/ MathOp /or/ Mov /or/ Mov2 /or/ Mov1 /or/ Push /or/ Pop /or/ FloatLoad /or/ FloatMath /or/ PureFloat) 
        return false;
    return couldFixup(inOp1(), shift) && couldFixup(inOp2(), shift) && couldFixup(outOp(), shift);
  }
  void fixupStack(int shift) {
    auto s1 = inOp1(), s2 = inOp2(), s3 = outOp();
    s1.fixupString(shift); s2.fixupString(shift); s3.fixupString(shift);
    if (inOp1()) inOp1 = s1;
    if (inOp2()) inOp2 = s2;
    if (outOp()) outOp = s3;
    if (tp.hasStackdepth)
      tp.stackdepth += shift;
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

static int si;

bool referencesStack(ref Transaction t, bool affects = false, bool active = false) {
  with (Transaction.Kind)
    if (t.kind == SAlloc /or/ SFree /or/ Call /or/ Compare /or/ Label /or/ Jump)
      return true;
    else if (t.kind == FloatMath /or/ PureFloat)
      return false;
    else if (affects && t.kind == Pop /or/ Push)
      return true;
  bool res;
  void test(ref string s) {
    if (s.isIndirect()) res |= true; // MAY access the stack.
    string stackreg, basereg;
    if (isARM) { stackreg = "sp"; basereg = "fp"; }
    else { stackreg = "%esp"; basereg = "%ebp"; }
    if (s.find(stackreg) != -1) { res |= true; return; }
    if (active) {
      int offs;
      if (s.isIndirect2(offs) == basereg) {
        res |= offs < 0; // negative ebp is active stack
      }
    } else {
      res |= s.find(basereg) != -1;
    }
  }
  if (affects) info(t).accessParams(&test, true);
  else         info(t).accessParams(&test);
  return res;
}

bool changesOrNeedsActiveStack(ref Transaction t) {
  return referencesStack(t, false, true) || referencesStack(t, true, true);
}

bool doesntWriteStack(ref Transaction t) {
  with (Transaction.Kind) {
    if (t.kind == FloatMath /or/ PureFloat /or/ FloatLoad) {
      return true;
    }
  }
  return false;
}

struct onceThenCall {
  void delegate(Transaction) dg;
  int opApply(int delegate(ref Transaction) _body) {
    Transaction tr;
    _body(tr);
    dg(tr);
    return 0;
  }
}

bool affectsStack(ref Transaction t) { return referencesStack(t, true); }

bool willOverwrite(ref Transaction t, string what) {
  if (!what.isRegister()) return false;
  bool res;
  info(t).accessParams((ref string s) { res |= s == what; }, true);
  return res;
}

bool pinsRegister(ref Transaction t, string reg) {
  with (Transaction.Kind)
    if (t.kind == Call /or/ Label /or/ Jump /or/ Compare /or/ FloatCompare /or/ ExtendDivide /* unsafe ones */)
      return true;
    else if (t.kind == FloatMath /or/ PureFloat)
      return false;
  if (auto reg2 = reg.isIndirect()) {
    // a transaction that only accesses (other) registers does not pin a memory write
    bool res;
    info(t).accessParams(delegate void(ref string s) {
      if (s.find(reg2) != -1) res = true;
      if (s.isIndirect()) res = true;
    });
    return res;
  }
  bool res;
  info(t).accessParams(delegate void(ref string s) {
    if (s.find(reg) != -1) res = true;
  });
  return res;
}

bool isUtilityRegister(string reg) {
  if (isARM) {
    if (auto rest = reg.startsWith("r")) {
      foreach (ch; rest) if (ch < '0' || ch > '9') return false;
      auto rid = std.string.atoi(rest);
      if (rid >= 0 && rid < 16) return true;
    }
    return false;
  }
  if (reg == "%eax"[] /or/ "%ebx"[] /or/ "%ecx"[] /or/ "%edx"[] /or/ "%edi"[])
    return true;
  return false;
}

string opt(string name, string s) {
  bool barrier;
  if (s.length >= 8 && s[0..8] == "barrier:") { barrier = true; s = s[8..$]; }
  string src = s.ctSlice("=>"), dest = s;
  string stmt_match = src.ctSlice(":");
  int instrs = 0;
  {
    string temp = stmt_match;
    while (true) {
      string match = temp.ctSlice(",").ctStrip();
      if (!match.length || match == "]") break;
      string instr_string = ctToString(instrs), str = "$" ~ instr_string, repl = "match["~instr_string~"]";
      src = src  .ctReplace(str, repl);
      dest = dest.ctReplace(str, repl);
      instrs ++;
    }
  }
  string res;
  res ~= `bool `~name~`(Transcache cache,ref int[string] l_refc) {
    bool _changed;
    auto match = cache.findMatch("`~name~`", (Transaction[] ls) {
      if (ls.length >= ` ~ ctToString(instrs);
  {
    string temp = stmt_match, merp; int i;
    while ((merp=temp.ctSlice(",")).length) {
      if (merp.ctStrip() == "*") i++;
      else if (merp.ctStrip() == "]")
        res ~= ` && (ls.length==` ~ ctToString(i) ~ `)`;
      else
        res ~= ` && (` ~ merp.ctStrip().ctReplace("^", `ls[` ~ ctToString(i++) ~ `].kind == Transaction.Kind.`) ~ `)`;
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
  if (name != "ext_step") // handled differently
    res ~= `
      if (xpar != -1 && si >= xpar) continue;
      si++;
      `;
  res ~= dest~`
      if (match.modded) {
        _changed = true;
      }
    } while (match.advance());
    return _changed;
  }
  opts ~= stuple(&`~name~`, "`~name~`", true, `; if (barrier) res ~= `true`; else res ~= `false`; res ~= `);`;
  res = res.ctReplace(
        "$SUBSTWITH", `foreach (ref $T res; onceThenCall(($T t) { match.replaceWith(t); })) with (res)`,
        "$SUBST", `match.replaceWith`,
        "$TK", `Transaction.Kind`,
        "$T", `Transaction`);
  return res;
}

bool optsSetup;
void setupGenericOpts() {
  synchronized {
    if (optsSetup) return;
    optsSetup = true;
  }
  mixin(opt("sort_mem", `*, ^SAlloc || ^SFree:
    (doesntWriteStack($0) || !referencesStack($0)) && !affectsStack($0)
    =>
    int delta;
    if ($1.kind == $TK.SAlloc) delta = $1.size;
    else if ($1.kind == $TK.SFree) delta = -$1.size;
    else assert(false);
    auto t2 = $0;
    if (info(t2).couldFixup(delta)) {
      info(t2).fixupStack(delta);
      $SUBST($1, t2);
    }
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
  mixin(opt("push_pop_is_mov_sometimes", `^Push, ^Pop:
    $0.size == 4 && $1.size == 4 && $1.dest.isUtilityRegister()
    =>
    $T t; t.kind = $TK.Mov; t.from = $0.source; t.to = $1.dest; t.stackdepth = $0.stackdepth;
    if (t.from == t.to) $SUBST();
    else $SUBST(t);
  `));
  mixin(opt("code_between_jump_and_label_is_dead", `^Jump, *:
    $1.kind != $TK.Label && !$0.mode
    =>
    $SUBST($0);
  `));
}
