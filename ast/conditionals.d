// conditionals, ie. if tests
module ast.conditionals;

import ast.base, ast.namespace, ast.parse, ast.math, tools.base: This, This_fn, rmSpace;

class TrueCond : Cond {
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    string toString() { return Format("true"[]); }
    void jumpOn(AsmFile af, bool cond, string dest) {
      if (cond) af.jump(dest);
    }
  }
}

class FalseCond : Cond {
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    string toString() { return Format("false"[]); }
    void jumpOn(AsmFile af, bool cond, string dest) {
      if (!cond) af.jump(dest);
    }
  }
}

class ExprWrap : Cond {
  Expr ex;
  this(Expr ex) {
    this.ex = ex;
    if (!ex) fail;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override {
    string toString() { return Format("!!"[], ex); }
    void jumpOn(AsmFile af, bool cond, string dest) {
      mixin(mustOffset("0"[]));
      ex.emitAsm(af);
      with (af) {
        popStack(regs[0], 4);
        compare(regs[0], regs[0], true);
        nvm(regs[0]);
        if (cond)
          jumpOn(true, false, true, dest); // Jump on !=0
        else
          jumpOn(false, true, false, dest); // jump on 0.
      }
    }
  }
}

class StatementAndCond : Cond {
  Statement first;
  Cond second;
  mixin MyThis!("first, second"[]);
  mixin DefaultDup!();
  mixin defaultIterate!(first, second);
  override {
    string toString() { return Format("{ "[], first, " "[], second, " }"[]); }
    void jumpOn(AsmFile af, bool cond, string dest) {
      mixin(mustOffset("0"[]));
      first.emitAsm(af);
      second.jumpOn(af, cond, dest);
    }
  }
}

const bool useIVariant = true;

class Compare : Cond, Expr {
  Expr e1; bool smaller, equal, greater; Expr e2;
  Expr falseOverride, trueOverride;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(e1, e2, falseOverride, trueOverride);
  string toString() {
    string res;
    if (smaller) res ~= "<";
    if (equal) res ~= "=";
    if (greater) res ~= ">";
    if (!smaller && !greater) res ~= "=";
    res ~= "(";
    res ~= (fastcast!(Object)~ e1).toString();
    res ~= ", ";
    res ~= (fastcast!(Object)~ e2).toString();
    res ~= ")";
    return res;
  }
  this(Expr e1, bool not, bool smaller, bool equal, bool greater, Expr e2) {
    if (e1.valueType().size != 4 /or/ 8) {
      logln("Invalid comparison parameter: "[], e1.valueType());
      fail;
    }
    if (e2.valueType().size != 4 /or/ 8) {
      logln("Invalid comparison parameter: "[], e2.valueType());
      fail;
    }
    if (not) {
      not = !not;
      smaller = !smaller;
      equal = !equal;
      greater = !greater;
    }
    this.e1 = e1;
    this.smaller = smaller; this.equal = equal; this.greater = greater;
    this.e2 = e2;
  }
  this(Expr e1, string str, Expr e2) {
    auto backup = str;
    bool not, smaller, greater, equal;
    if (auto rest = str.startsWith("!"[])) { not =      true; str = rest; }
    if (auto rest = str.startsWith("<"[])) { smaller =  true; str = rest; }
    if (auto rest = str.startsWith(">"[])) { greater =  true; str = rest; }
    if (!not && !smaller && !greater) {
      if (auto rest = str.startsWith("=="[])) { equal = true; str = rest; }
    } else {
      if (auto rest = str.startsWith("="[])) { equal =  true; str = rest; }
    }
    if (str.length)
      throw new Exception("Not a valid condition string: "~backup~". "[]);
    this(e1, not, smaller, equal, greater, e2);
  }
  void flip() {
    swap(e1, e2);
    swap(smaller, greater);
  }
  bool isFloat() {
    return !!(Single!(Float) == e1.valueType());
  }
  bool isDouble() {
    return !!(Single!(Double) == e1.valueType());
  }
  void prelude() {
    assert(e1.valueType().size == 4 /or/ 8);
    assert(e2.valueType().size == 4 /or/ 8);
    if (fastcast!(IntExpr) (e1) && !fastcast!(IntExpr) (e2))
      flip;
    if (Single!(Float) == e1.valueType() && Single!(Float) != e2.valueType()) {
      assert(Single!(SysInt) == e2.valueType());
      e2 = fastalloc!(IntAsFloat)(e2);
    }
    if (Single!(Float) == e2.valueType() && Single!(Float) != e1.valueType()) {
      assert(Single!(SysInt) == e1.valueType());
      e1 = fastalloc!(IntAsFloat)(e1);
    }
  }
  private void emitComparison(AsmFile af) { with (af) {
    mixin(mustOffset("0"[]));
    prelude;
    if (isARM) {
      if (isDouble) {
        fail;
        return;
      }
      if (isFloat) {
        fail;
        return;
      }
    }
    if (isDouble) {
      e2.emitAsm(af); loadDouble("(%esp)"[]); sfree(8);
      e1.emitAsm(af); loadDouble("(%esp)"[]); sfree(8);
      compareFloat("%st(1)"[], useIVariant);
    } else if (isFloat) {
      e2.emitAsm(af); loadFloat("(%esp)"[]); sfree(4);
      e1.emitAsm(af); loadFloat("(%esp)"[]); sfree(4);
      compareFloat("%st(1)"[], useIVariant);
      // e1.emitAsm(af); e2.emitAsm(af);
      // SSEOp("movd"[], "(%esp)"[], "%xmm1"[], true /* ignore alignment */); sfree(4);
      // SSEOp("movd"[], "(%esp)"[], "%xmm0"[], true); sfree(4);
      // SSEOp("comiss"[], "%xmm1"[], "%xmm0"[]);
    } else if (auto ie = fastcast!(IntExpr) (e2)) {
      e1.emitAsm(af);
      popStack(regs[0], 4);
      compare(regs[0], number(ie.num));
    } else {
      e2.emitAsm(af);
      e1.emitAsm(af);
      popStack(regs[3], 4);
      popStack(regs[0], 4);
      compare(regs[3], regs[0]);
    }
  }}
  override {
    IType valueType() {
      if (falseOverride && trueOverride) {
        assert(falseOverride.valueType() == trueOverride.valueType());
        return falseOverride.valueType();
      }
      return Single!(SysInt);
    }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("valueType().size"[]));
      if (falseOverride && trueOverride) {
        falseOverride.emitAsm(af);
        trueOverride.emitAsm(af);
      }
      emitComparison(af);
      if (isARM) { af.put("mrs r0, cpsr"[]); }
      auto s = smaller, e = equal, g = greater;
      if (falseOverride && trueOverride) {
        if (isARM) {
          af.mmove4("[sp]"[], "r3"[]);
          af.mmove4("[sp,#4]"[], "r2"[]);
        } else {
          // DO NOT POP! POP IS MOVE/SFREE! SFREE OVERWRITES COMPARISON!
          af.mmove4( "(%esp)"[], "%edx"[]);
          af.mmove4("4(%esp)"[], "%ecx"[]);
        }
      } else {
        af.mmove4(af.number(1), af.regs[3]);
        af.mmove4(af.number(0), af.regs[2]);
      }
      if (isARM) { af.put("msr cpsr, r0"[]); }
      // can't use eax, moveOnFloat needs ax .. or does it? (SSE mode)
      if (isFloat || isDouble)
        af.moveOnFloat(s, e, g, af.regs[3], af.regs[2], /* convert */ !useIVariant);
      else
        af.cmov(s, e, g, af.regs[3], af.regs[2]);
      // now can safely free.
      if (falseOverride && trueOverride)
        af.sfree(8);
      af.pushStack(af.regs[2], 4);
    }
    void jumpOn(AsmFile af, bool cond, string dest) {
      emitComparison(af);
      auto s = smaller, e = equal, g = greater;
      if (!cond) { // negate
        s = !s; e = !e; g = !g; // TODO: validate
      }
      if (isFloat || isDouble)
        af.jumpOnFloat(s, e, g, dest, /* convert */ !useIVariant);
      else
        af.jumpOn(s, e, g, dest);
    }
  }
}

Object gotIntExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr res;
  IType[] its;
  if (!rest(text, "tree.expr"[], &res))
    return null;
  if (!gotImplicitCast(res, (IType it) { its ~= it; return it.size == 4; })) {
    text.setError("Neither of those was int sized: "[], its);
    return null;
  }
  return fastcast!(Object)~ res;
}
mixin DefaultParser!(gotIntExpr, "tree.int_expr"[]);

class NegCond : Cond {
  Cond c;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(c);
  this(Cond c) { this.c = c; if (!c) fail; }
  override string toString() { return Format("!("[], c, ")"[]); }
  override void jumpOn(AsmFile af, bool cond, string dest) {
    c.jumpOn(af, !cond, dest);
  }
}

Object gotNegate(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond c;
  if (!rest(t2, "cond >cond.bin"[], &c))
    t2.failparse("Couldn't match condition to negate"[]);
  text = t2;
  return fastalloc!(NegCond)(c);
}
mixin DefaultParser!(gotNegate, "cond.negate"[], "6"[], "!"[]);

Cond compare(string op, Expr ex1, Expr ex2) {
  bool not, smaller, equal, greater;
  string op2 = op;
  while (op2.length) {
    if (op2[0] == '!') { not     = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '<') { smaller = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '=') { equal   = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '>') { greater = true; op2 = op2[1 .. $]; continue; }
    fail;
  }
  {
    auto ie1 = ex1, ie2 = ex2;
    bool isInt(IType it) { return !!fastcast!(SysInt) (resolveType(it)); }
    if (gotImplicitCast(ie1, Single!(SysInt), &isInt) && gotImplicitCast(ie2, Single!(SysInt), &isInt)) {
      return fastalloc!(Compare)(ie1, not, smaller, equal, greater, ie2);
    }
  }
  {
    auto fe1 = ex1, fe2 = ex2;
    bool isFloat(IType it) { return !!fastcast!(Float) (resolveType(it)); }
    if (gotImplicitCast(fe1, Single!(Float), &isFloat) && gotImplicitCast(fe2, Single!(Float), &isFloat)) {
      return fastalloc!(Compare)(fe1, not, smaller, equal, greater, fe2);
    }
  }
  {
    auto de1 = ex1, de2 = ex2;
    bool isDouble(IType it) { return !!fastcast!(Double) (resolveType(it)); }
    if (gotImplicitCast(de1, Single!(Double), &isDouble) && gotImplicitCast(de2, Single!(Double), &isDouble)) {
      return fastalloc!(Compare)(de1, not, smaller, equal, greater, de2);
    }
  }
  return fastalloc!(ExprWrap)(lookupOp(op, ex1, ex2));
}

import ast.modules;
Expr True, False;
Cond cTrue, cFalse;
void setupStaticBoolLits() {
  if (True && False) return;
  True = fastcast!(Expr) (sysmod.lookup("true"[]));
  False = fastcast!(Expr) (sysmod.lookup("false"[]));
  cTrue = new TrueCond;
  cFalse = new FalseCond;
}

import ast.fold;
bool isStaticTrue(Cond cd) {
  if (fastcast!(TrueCond) (cd)) return true;
  auto ew = fastcast!(ExprWrap) (cd);
  if (!ew) return false;
  return ew.ex is True;
}

bool isStaticFalse(Cond cd) {
  if (fastcast!(FalseCond) (cd)) return true;
  auto ew = fastcast!(ExprWrap) (cd);
  if (!ew) return false;
  return ew.ex is False;
}

import ast.casting, ast.opers;
Object gotCompare(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool not, smaller, equal, greater;
  Expr ex1, ex2; Cond cd2;
  if (!rest(t2, "tree.expr _tree.expr.cond"[], &ex1)) return null;
  // oopsie-daisy, iterator assign is not the same as "smaller than negative"!
  if (t2.acceptLeftArrow()) return null;
  if (t2.accept("!"[])) not = true;
  if (t2.accept("<"[])) smaller = true;
  if (t2.accept(">"[])) greater = true;
  if ((not || smaller || greater) && t2.accept("="[]) || t2.accept("=="[]))
    equal = true;
  
  if (!not && !smaller && !greater && !equal)
    return null;
  
  if (!rest(t2, "cond.compare"[], &cd2) && // chaining
      !rest(t2, "tree.expr _tree.expr.cond"[], &ex2)) {
    t2.failparse("Could not parse second operator for comparison"[]);
  }
  auto finalize = delegate Cond(Cond cd) { return cd; };
  if (cd2) {
    if (auto cmp2 = fastcast!(Compare) (cd2)) {
      ex2 = cmp2.e1;
      finalize = cmp2 /apply/ delegate Cond(Compare cmp2, Cond cd) {
        return new BooleanOp!("&&"[])(cd, cmp2);
      };
    } else {
      text.failparse("can't chain condition: "[], cd2);
      return null;
    }
  }
  auto op = (not?"!":""[])~(smaller?"<":""[])~(greater?">":""[])~(equal?"=":""[]);
  if (op == "="[]) op = "==";
  try {
    auto res = fastcast!(Object) (finalize(compare(op, ex1, ex2)));
    if (!res) text.failparse("Undefined comparison"[]);
    text = t2;
    return res;
  } catch (Exception ex) {
    text.failparse(ex);
  }
}
mixin DefaultParser!(gotCompare, "cond.compare"[], "71"[]);

import ast.literals;
class BooleanOp(string Which) : Cond, HasInfo {
  Cond c1, c2;
  mixin MyThis!("c1, c2"[]);
  mixin DefaultDup!();
  mixin defaultIterate!(c1, c2);
  override {
    string getInfo()  { return Which; }
    string toString() { return Format(Which, "("[], c1, ", "[], c2, ")"[]); }
    void jumpOn(AsmFile af, bool cond, string dest) {
      static if (Which == "&&"[]) {
        if (cond) {
          auto past = af.genLabel();
          c1.jumpOn(af, false, past);
          c2.jumpOn(af, true, dest);
          af.emitLabel(past, !keepRegs, isForward);
        } else {
          c1.jumpOn(af, false, dest);
          c2.jumpOn(af, false, dest);
        }
      } else
      static if (Which == "||"[]) {
        if (cond) {
          c1.jumpOn(af, true, dest);
          c2.jumpOn(af, true, dest);
        } else {
          auto past = af.genLabel();
          c1.jumpOn(af, true, past);
          c2.jumpOn(af, false, dest);
          af.emitLabel(past, !keepRegs, isForward);
        }
      } else
      static assert(false, "unknown boolean op: "~Which);
    }
  }
}

alias BooleanOp!("&&"[]) AndOp;
alias BooleanOp!("||"[]) OrOp;

Object gotBoolOp(string Op, alias Class)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (!cont(t2, &cd)) return null;
  auto old_cd = cd;
  while (t2.accept(Op)) {
    Cond cd2;
    if (!cont(t2, &cd2))
      t2.failparse("Couldn't get second cond after '"[], Op, "'"[]);
    cd = fastalloc!(Class)(cd, cd2);
  }
  if (old_cd is cd) return null;
  text = t2;
  return fastcast!(Object)~ cd;
}
mixin DefaultParser!(gotBoolOp!("&&"[], AndOp), "cond.bin.and"[], "2"[]);
mixin DefaultParser!(gotBoolOp!("||"[], OrOp), "cond.bin.or"[], "1"[]);
static this() {
  parsecon.addPrecedence("cond.bin"[], "5"[]);
}

Object gotBraces(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (rest(t2, "cond"[], &cd) && t2.accept(")"[])) {
    text = t2;
    return fastcast!(Object)~ cd;
  } else return null;
}
mixin DefaultParser!(gotBraces, "cond.braces"[], "74"[], "("[]);

// pretty much only needed for iparses that use conds
Object gotNamedCond(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string id;
  if (!t2.gotIdentifier(id)) return null;
  retry:
  if (auto cd = fastcast!(Cond) (namespace().lookup(id))) {
    text = t2;
    return fastcast!(Object)~ cd;
  } else if (t2.eatDash(id)) goto retry;
  else return null;
}
mixin DefaultParser!(gotNamedCond, "cond.named"[], "75"[]);

import ast.vardecl;
class CondExpr : Expr {
  Cond cd;
  this(Cond cd) {
    this.cd = cd;
    if (!cd) fail;
  }
  mixin defaultIterate!(cd);
  override {
    string toString() { return Format("eval "[], cd); }
    IType valueType() { return fastcast!(IType) (sysmod.lookup("bool"[])); }
    CondExpr dup() { return fastalloc!(CondExpr)(cd.dup); }
    void emitAsm(AsmFile af) {
      if (auto ex = cast(Expr) cd) {
        ex.emitAsm(af);
      } else {
        mkVar(af, Single!(SysInt), true, (Variable var) {
          mixin(mustOffset("0"[]));
          iparse!(Statement, "cond_expr_ifstmt"[], "tree.stmt"[])
                (`if !cond { var = false;} else {var = true;} `,
                  "cond"[], cd, "var"[], var, af).emitAsm(af);
        });
      }
    }
  }
}

Object gotCondAsExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (!rest(t2, "cond"[], &cd)) return null;
  text = t2;
  if (auto ew = fastcast!(ExprWrap) (cd)) {
    return fastcast!(Object) (ew.ex);
  }
  return fastalloc!(CondExpr)(cd);
}
mixin DefaultParser!(gotCondAsExpr, "tree.expr.eval.cond"[], null, "eval"[]);

Object gotComplexCondAsExpr(bool mode)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if ((!mode || !rest(t2, "cond.compare"[], &cd) && !rest(t2, "cond.negate"[], &cd))
   && ( mode || !rest(t2, "cond.iter_very_strict"[], &cd))) return null;
  text = t2;
  if (auto ew = fastcast!(ExprWrap) (cd)) {
    return fastcast!(Object) (ew.ex);
  }
  return fastalloc!(CondExpr)(cd);
}
mixin DefaultParser!(gotComplexCondAsExpr!(true),  "tree.expr.cond.compare_negate"[], "1"[]);
mixin DefaultParser!(gotComplexCondAsExpr!(false), "tree.expr.cond_other"[], "13"[]);
static this() {
  parsecon.addPrecedence("tree.expr.cond"[], "120"[]);
}

Expr longOp(string Code)(Expr e1, Expr e2) {
  bool isLong(Expr ex) { return test(Single!(Long) == resolveType(ex.valueType())); }
  if (!isLong(e1) && !isLong(e2))
    return null;
  if (!gotImplicitCast(e1, &isLong) || !gotImplicitCast(e2, &isLong))
    return null;
  auto pair = mkTuple(Single!(SysInt), Single!(SysInt));
  return fastalloc!(CondExpr)(
    iparse!(Cond, "long_op"[], "cond"[])
           (Code,
            "a"[], reinterpret_cast(pair, e1), "b"[], reinterpret_cast(pair, e2))
  );
}

import ast.tuples;
static this() {
  defineOp("!="[], delegate Expr(Expr ex1, Expr ex2) {
    if (auto op = lookupOp("=="[], true, ex1, ex2)) {
      return fastalloc!(CondExpr)(fastalloc!(NegCond)(fastalloc!(ExprWrap)(op)));
    }
    return null;
  });
  // TODO: generalize to save 15 lines or so
  defineOp("<"[], delegate Expr(Expr ex1, Expr ex2) { return longOp!(`(a[1] < b[1]) || (a[1] == b[1] && (a[0] < b[0]))`)(ex1, ex2); });
  defineOp(">"[], delegate Expr(Expr ex1, Expr ex2) { return longOp!(`(a[1] > b[1]) || (a[1] == b[1] && (a[0] > b[0]))`)(ex1, ex2); });
  defineOp("=="[],delegate Expr(Expr ex1, Expr ex2) { return longOp!(`a[0] == b[0] && a[1] == b[1]`)(ex1, ex2); });
}
