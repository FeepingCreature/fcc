// conditionals, ie. if tests
module ast.conditionals;

import ast.base, ast.namespace, ast.parse, ast.math, tools.base: This, This_fn, rmSpace;

class ExprWrap : Cond {
  Expr ex;
  mixin MyThis!("ex");
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override {
    string toString() { return Format("!!", ex); }
    void jumpOn(AsmFile af, bool cond, string dest) {
      ex.emitAsm(af);
      af.popStack("%eax", 4);
      af.compare("%eax", "%eax", true);
      af.nvm("%eax");
      if (cond)
        af.jumpOn(true, false, true, dest); // Jump on !=0
      else
        af.jumpOn(false, true, false, dest); // jump on 0.
    }
  }
}

class StatementAndCond : Cond {
  Statement first;
  Cond second;
  mixin MyThis!("first, second");
  mixin DefaultDup!();
  mixin defaultIterate!(first, second);
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      first.emitAsm(af);
      second.jumpOn(af, cond, dest);
    }
  }
}

class Compare : Cond, Expr {
  Expr e1; bool smaller, equal, greater; Expr e2;
  Expr falseOverride, trueOverride;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(e1, e2, falseOverride, trueOverride);
  string toString() {
    auto res = (fastcast!(Object)~ e1).toString();
    if (smaller) res ~= "<";
    if (equal) res ~= "=";
    if (greater) res ~= ">";
    if (!smaller && !greater) res ~= "=";
    res ~= (fastcast!(Object)~ e2).toString();
    return res;
  }
  this(Expr e1, bool not, bool smaller, bool equal, bool greater, Expr e2) {
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
    if (auto rest = str.startsWith("!")) { not =      true; str = rest; }
    if (auto rest = str.startsWith("<")) { smaller =  true; str = rest; }
    if (auto rest = str.startsWith(">")) { greater =  true; str = rest; }
    if (!not && !smaller && !greater) {
      if (auto rest = str.startsWith("==")) { equal = true; str = rest; }
    } else {
      if (auto rest = str.startsWith("=")) { equal =  true; str = rest; }
    }
    if (str.length)
      throw new Exception("Not a valid condition string: "~backup~". ");
    this(e1, not, smaller, equal, greater, e2);
  }
  void flip() {
    swap(e1, e2);
    swap(smaller, greater);
  }
  bool isFloat() {
    return !!(Single!(Float) == e1.valueType());
  }
  void prelude() {
    assert(e1.valueType().size == 4);
    assert(e2.valueType().size == 4);
    if (fastcast!(IntExpr) (e1) && !fastcast!(IntExpr) (e2))
      flip;
    if (Single!(Float) == e1.valueType() && Single!(Float) != e2.valueType()) {
      assert(Single!(SysInt) == e2.valueType());
      e2 = new IntAsFloat(e2);
    }
    if (Single!(Float) == e2.valueType() && Single!(Float) != e1.valueType()) {
      assert(Single!(SysInt) == e1.valueType());
      e1 = new IntAsFloat(e1);
    }
  }
  void emitComparison(AsmFile af) {
    prelude;
    if (isFloat) {
      e2.emitAsm(af); af.loadFloat("(%esp)"); af.sfree(4);
      e1.emitAsm(af); af.loadFloat("(%esp)"); af.sfree(4);
      af.compareFloat("%st1");
      // e1.emitAsm(af); e2.emitAsm(af);
      // af.SSEOp("movd", "(%esp)", "%xmm1", true /* ignore alignment */); af.sfree(4);
      // af.SSEOp("movd", "(%esp)", "%xmm0", true); af.sfree(4);
      // af.SSEOp("comiss", "%xmm1", "%xmm0");
    } else if (auto ie = fastcast!(IntExpr) (e2)) {
      e1.emitAsm(af);
      af.popStack("%eax", 4);
      // remember: at&t order is inverted
      af.compare(Format("$", ie.num), "%eax");
    } else {
      e2.emitAsm(af);
      e1.emitAsm(af);
      af.popStack("%edx", 4);
      af.popStack("%eax", 4);
      af.compare("%eax", "%edx");
    }
  }
  override {
    IType valueType() {
      if (falseOverride && trueOverride) {
        assert(falseOverride.valueType() == trueOverride.valueType());
        return falseOverride.valueType();
      }
      return Single!(SysInt);
    }
    void emitAsm(AsmFile af) {
      if (falseOverride && trueOverride) {
        falseOverride.emitAsm(af);
        trueOverride.emitAsm(af);
      }
      emitComparison(af);
      auto s = smaller, e = equal, g = greater;
      if (falseOverride && trueOverride) {
        // DO NOT POP! POP IS MOVE/SFREE! SFREE OVERWRITES COMPARISON!
        af.mmove4( "(%esp)", "%edx");
        af.mmove4("4(%esp)", "%ecx");
      } else {
        af.mmove4("$1", "%edx");
        af.mmove4("$0", "%ecx"); // don't xorl; mustn't overwrite comparison results
      }
      // can't use eax, moveOnFloat needs ax .. or does it? (SSE mode)
      if (isFloat) af.moveOnFloat(s, e, g, "%edx", "%ecx", /*true*/ /* is SSE */ false);
      else af.cmov(s, e, g, "%edx", "%ecx");
      // now can safely free.
      if (falseOverride && trueOverride)
        af.sfree(8);
      af.pushStack("%ecx", 4);
    }
    void jumpOn(AsmFile af, bool cond, string dest) {
      emitComparison(af);
      auto s = smaller, e = equal, g = greater;
      if (!cond) { // negate
        s = !s; e = !e; g = !g; // TODO: validate
        /*swap(s, g);
        if (s + g == 1)
          e = !e;*/
      }
      if (isFloat) af.jumpOnFloat(s, e, g, dest, /*true*/ /* is SSE also */ false);
      else af.jumpOn(s, e, g, dest);
    }
  }
}

Object gotIntExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr res;
  IType[] its;
  if (!rest(text, "tree.expr", &res))
    return null;
  if (!gotImplicitCast(res, (IType it) { its ~= it; return it.size == 4; })) {
    text.setError("Neither of those was int sized: ", its);
    return null;
  }
  return fastcast!(Object)~ res;
}
mixin DefaultParser!(gotIntExpr, "tree.int_expr");

class NegCond : Cond {
  Cond c;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(c);
  this(Cond c) { this.c = c; }
  override void jumpOn(AsmFile af, bool cond, string dest) {
    c.jumpOn(af, !cond, dest);
  }
}

Object gotNegate(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond c;
  if (!rest(t2, "cond >cond.bin", &c))
    t2.failparse("Couldn't match condition to negate");
  text = t2;
  return new NegCond(c);
}
mixin DefaultParser!(gotNegate, "cond.negate", "72", "!");

Cond compare(string op, Expr ex1, Expr ex2) {
  bool not, smaller, equal, greater;
  string op2 = op;
  while (op2.length) {
    if (op2[0] == '!') { not     = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '<') { smaller = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '=') { equal   = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '>') { greater = true; op2 = op2[1 .. $]; continue; }
    asm { int 3; }
  }
  {
    auto ie1 = ex1, ie2 = ex2;
    bool isInt(IType it) { return !!fastcast!(SysInt) (resolveType(it)); }
    if (gotImplicitCast(ie1, &isInt) && gotImplicitCast(ie2, &isInt)) {
      return new Compare(ie1, not, smaller, equal, greater, ie2);
    }
  }
  {
    auto fe1 = ex1, fe2 = ex2;
    bool isFloat(IType it) { return !!fastcast!(Float) (resolveType(it)); }
    if (gotImplicitCast(fe1, &isFloat) && gotImplicitCast(fe2, &isFloat)) {
      return new Compare(fe1, not, smaller, equal, greater, fe2);
    }
  }
  return new ExprWrap(lookupOp(op, ex1, ex2));
}

import ast.modules;
Expr True, False;
Cond cTrue, cFalse;
void setupStaticBoolLits() {
  if (True && False) return;
  True = fastcast!(Expr) (sysmod.lookup("true"));
  False = fastcast!(Expr) (sysmod.lookup("false"));
  cTrue = new ExprWrap (True);
  cFalse = new ExprWrap (False);
}

import ast.fold;
bool isStaticTrue(Cond cd) {
  auto ew = fastcast!(ExprWrap) (cd);
  if (!ew) return false;
  return ew.ex is True;
}

bool isStaticFalse(Cond cd) {
  auto ew = fastcast!(ExprWrap) (cd);
  if (!ew) return false;
  return ew.ex is False;
}

import ast.casting, ast.opers;
Object gotCompare(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool not, smaller, equal, greater;
  Expr ex1, ex2; Cond cd2;
  if (!rest(t2, "tree.expr >tree.expr.cond", &ex1)) return null;
  // oopsie-daisy, iterator assign is not the same as "smaller than negative"!
  if (t2.accept("<-")) return null;
  if (t2.accept("!")) not = true;
  if (t2.accept("<")) smaller = true;
  if (t2.accept(">")) greater = true;
  if ((not || smaller || greater) && t2.accept("=") || t2.accept("=="))
    equal = true;
  
  if (!not && !smaller && !greater && !equal)
    return null;
  
  if (!rest(t2, "cond.compare", &cd2) && // chaining
      !rest(t2, "tree.expr >tree.expr.cond", &ex2) ) return null;
  auto finalize = delegate Cond(Cond cd) { return cd; };
  if (cd2) {
    if (auto cmp2 = fastcast!(Compare) (cd2)) {
      ex2 = cmp2.e1;
      finalize = cmp2 /apply/ delegate Cond(Compare cmp2, Cond cd) {
        return new BooleanOp!("&&")(cd, cmp2);
      };
    } else {
      text.failparse("can't chain condition: ", cd2);
      return null;
    }
  }
  text = t2;
  auto op = (not?"!":"")~(smaller?"<":"")~(greater?">":"")~(equal?"=":"");
  if (op == "=") op = "==";
  return fastcast!(Object) (finalize(compare(op, ex1, ex2)));
}
mixin DefaultParser!(gotCompare, "cond.compare", "71");

import ast.literals;
class BooleanOp(string Which) : Cond, HasInfo {
  Cond c1, c2;
  mixin MyThis!("c1, c2");
  mixin DefaultDup!();
  mixin defaultIterate!(c1, c2);
  override {
    string getInfo()  { return Which; }
    void jumpOn(AsmFile af, bool cond, string dest) {
      static if (Which == "&&") {
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
      static if (Which == "||") {
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

alias BooleanOp!("&&") AndOp;
alias BooleanOp!("||") OrOp;

Object gotBoolOp(string Op, alias Class)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (!cont(t2, &cd)) return null;
  auto old_cd = cd;
  while (t2.accept(Op)) {
    Cond cd2;
    if (!cont(t2, &cd2))
      t2.failparse("Couldn't get second cond after '", Op, "'");
    cd = new Class(cd, cd2);
  }
  if (old_cd is cd) return null;
  text = t2;
  return fastcast!(Object)~ cd;
}
mixin DefaultParser!(gotBoolOp!("&&", AndOp), "cond.bin.and", "2");
mixin DefaultParser!(gotBoolOp!("||", OrOp), "cond.bin.or", "1");
static this() {
  parsecon.addPrecedence("cond.bin", "5");
}

Object gotBraces(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (rest(t2, "cond", &cd) && t2.accept(")")) {
    text = t2;
    return fastcast!(Object)~ cd;
  } else return null;
}
mixin DefaultParser!(gotBraces, "cond.braces", "74", "(");

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
mixin DefaultParser!(gotNamedCond, "cond.named", "75");

import ast.vardecl;
class CondExpr : Expr {
  Cond cd;
  this(Cond cd) { this.cd = cd; }
  mixin defaultIterate!(cd);
  override {
    string toString() { return Format("eval ", cd); }
    IType valueType() { return Single!(SysInt); }
    CondExpr dup() { return new CondExpr(cd.dup); }
    void emitAsm(AsmFile af) {
      if (auto ex = cast(Expr) cd) {
        ex.emitAsm(af);
      } else {
        mkVar(af, Single!(SysInt), true, (Variable var) {
          mixin(mustOffset("0"));
          iparse!(Statement, "cond_expr_ifstmt", "tree.stmt")
                (`if !cond var = false; else var = true; `,
                  "cond", cd, "var", var, af).emitAsm(af);
        });
      }
    }
  }
}

Object gotCondAsExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (!rest(t2, "cond", &cd)) return null;
  text = t2;
  if (auto ew = fastcast!(ExprWrap) (cd)) {
    return fastcast!(Object) (ew.ex);
  }
  return new CondExpr(cd);
}
mixin DefaultParser!(gotCondAsExpr, "tree.expr.eval.cond", null, "eval");

Expr longOp(string Code)(Expr e1, Expr e2) {
  bool isLong(Expr ex) { return test(Single!(Long) == resolveType(ex.valueType())); }
  if (!isLong(e1) && !isLong(e2))
    return null;
  if (!gotImplicitCast(e1, &isLong) || !gotImplicitCast(e2, &isLong))
    return null;
  auto pair = mkTuple(Single!(SysInt), Single!(SysInt));
  return new CondExpr(
    iparse!(Cond, "long_op", "cond")
           (Code,
            "a", reinterpret_cast(pair, e1), "b", reinterpret_cast(pair, e2))
  );
}

import ast.tuples;
static this() {
  defineOp("!=", delegate Expr(Expr ex1, Expr ex2) {
    if (auto op = lookupOp("==", true, ex1, ex2)) {
      return new CondExpr(new NegCond(new ExprWrap(op)));
    }
    return null;
  });
  // TODO: generalize to save 15 lines or so
  defineOp("<", delegate Expr(Expr ex1, Expr ex2) { return longOp!(`(a[1] < b[1]) || (a[1] == b[1] && (a[0] < b[0]))`)(ex1, ex2); });
  defineOp(">", delegate Expr(Expr ex1, Expr ex2) { return longOp!(`(a[1] > b[1]) || (a[1] == b[1] && (a[0] > b[0]))`)(ex1, ex2); });
  defineOp("==",delegate Expr(Expr ex1, Expr ex2) { return longOp!(`a[0] == b[0] && a[1] == b[1]`)(ex1, ex2); });
}
