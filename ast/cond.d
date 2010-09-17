module ast.cond;

import ast.base, ast.namespace, ast.parse, ast.math, tools.base: This, This_fn, rmSpace;

class ExprWrap : Cond {
  Expr ex;
  mixin MyThis!("ex");
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      ex.emitAsm(af);
      af.popStack("%eax", ex.valueType());
      af.compare("%eax", "%eax", true);
      if (cond)
        af.jumpOn(true, false, true, dest); // Jump on !=0
      else
        af.jumpOn(false, true, false, dest); // jump on 0.
    }
  }
}

class Compare : Cond {
  Expr e1; bool smaller, equal, greater; Expr e2;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(e1, e2);
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
  void flip() {
    swap(e1, e2);
    smaller = !smaller;
    greater = !greater;
    equal = !equal;
  }
  bool isFloat() {
    return !!(Single!(Float) == e1.valueType());
  }
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      
      if (cast(IntExpr) e1 && !cast(IntExpr) e2)
        flip;
      
      if (Single!(Float) == e1.valueType() && Single!(Float) != e2.valueType()) {
        assert(Single!(SysInt) == e2.valueType());
        e2 = new IntAsFloat(e2);
      }
      if (Single!(Float) == e2.valueType() && Single!(Float) != e1.valueType()) {
        assert(Single!(SysInt) == e1.valueType());
        e1 = new IntAsFloat(e1);
      }
      
      if (isFloat) {
        e2.emitAsm(af);
        af.loadFloat("(%esp)");
        af.sfree(4);
        e1.emitAsm(af);
        af.loadFloat("(%esp)");
        af.sfree(4);
        af.put("fucompp"); af.floatStackDepth -= 2;
      } else if (auto ie = cast(IntExpr) e2) {
        e1.emitAsm(af);
        af.popStack("%eax", e1.valueType());
        // remember: at&t order is inverted
        af.compare(Format("$", ie.num), "%eax");
      } else {
        e2.emitAsm(af);
        e1.emitAsm(af);
        af.popStack("%ebx", e1.valueType());
        af.popStack("%eax", e2.valueType());
        af.compare("%eax", "%ebx");
      }
      auto s = smaller, e = equal, g = greater;
      if (!cond) { // negate
        s = !s; e = !e; g = !g; // TODO: validate
        /*swap(s, g);
        if (s + g == 1)
          e = !e;*/
      }
      if (isFloat) af.jumpOnFloat(s, e, g, dest);
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
    error = Format("Neither of those was int sized: ", its, " at ", text.next_text());
    return null;
  }
  return cast(Object) res;
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
  if (!t2.accept("!")) return null;
  Cond c;
  if (!rest(t2, "cond", &c))
    throw new Exception("Couldn't match condition to negate at '"~t2.next_text()~"'! ");
  text = t2;
  return new NegCond(c);
}
mixin DefaultParser!(gotNegate, "cond.negate", "72");

import ast.casting, ast.opers;
Object gotCompare(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool not, smaller, equal, greater;
  Expr ex1, ex2;
  if (rest(t2, "tree.expr >tree.expr.cond", &ex1) &&
      (
        (t2.accept("!") && (not = true)),
        (t2.accept("<") && (smaller = true)),
        (t2.accept(">") && (greater = true)),
        ((not || smaller || t2.accept("=")) && t2.accept("=") && (equal = true)),
        (smaller || equal || greater)
      ) && rest(t2, "tree.expr >tree.expr.cond", &ex2)
  ) {
    text = t2;
    {
      auto ie1 = ex1, ie2 = ex2;
      bool isInt(IType it) { return !!cast(SysInt) it; }
      if (gotImplicitCast(ie1, &isInt) && gotImplicitCast(ie2, &isInt)) {
        return new Compare(ie1, not, smaller, equal, greater, ie2);
      }
    }
    {
      auto fe1 = ex1, fe2 = ex2;
      bool isFloat(IType it) { return !!cast(Float) it; }
      if (gotImplicitCast(fe1, &isFloat) && gotImplicitCast(fe2, &isFloat)) {
        return new Compare(fe1, not, smaller, equal, greater, fe2);
      }
    }
    auto op = (not?"!":"")~(smaller?"<":"")~(greater?">":"")~(equal?"=":"");
    if (op == "=") op = "==";
    auto res = lookupOp(op, ex1, ex2);
    if (auto ce = cast(CondExpr) res) return cast(Object) ce.cd;
    logln("::", res);
    assert(false);
  } else return null;
}
mixin DefaultParser!(gotCompare, "cond.compare", "71");

import ast.literals, ast.casting;
Object gotExprAsCond(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (rest(t2, "<tree.expr >tree.expr.cond", &ex) && gotImplicitCast(ex, (IType it) { return it.size == 4; })) {
    // assert(ex.valueType().size == 4, Format(ex, ", being ", ex.valueType(), ", is a bad cond expr to test for at '", text.next_text(), "'. "));
    text = t2;
    return new ExprWrap(ex);
  } else return null;
}
mixin DefaultParser!(gotExprAsCond, "cond.expr", "73");

class BooleanOp(string Which) : Cond {
  Cond c1, c2;
  mixin MyThis!("c1, c2");
  mixin DefaultDup!();
  mixin defaultIterate!(c1, c2);
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      static if (Which == "&&") {
        if (cond) {
          auto past = af.genLabel();
          c1.jumpOn(af, false, past);
          c2.jumpOn(af, true, dest);
          af.emitLabel(past);
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
          af.emitLabel(past);
        }
      } else
      static assert(false, "unknown boolean op: "~Which);
    }
  }
}

Object gotBoolOp(string Op)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (!cont(t2, &cd)) return null;
  auto old_cd = cd;
  while (t2.accept(Op)) {
    Cond cd2;
    if (!cont(t2, &cd2))
      throw new Exception("Couldn't get second cond after '"
        ~ Op ~ "' at '"~t2.next_text()~"'");
    cd = new BooleanOp!(Op)(cd, cd2);
  }
  if (old_cd is cd) return null;
  text = t2;
  return cast(Object) cd;
}
mixin DefaultParser!(gotBoolOp!("&&"), "cond.bool_and", "6");
mixin DefaultParser!(gotBoolOp!("||"), "cond.bool_or", "5");

Object gotBraces(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (t2.accept("(") && rest(t2, "cond", &cd) && t2.accept(")")) {
    text = t2;
    return cast(Object) cd;
  } else return null;
}
mixin DefaultParser!(gotBraces, "cond.braces", "9");

// pretty much only needed for iparses that use conds
Object gotNamedCond(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string id;
  if (!t2.gotIdentifier(id)) return null;
  if (auto cd = cast(Cond) namespace().lookup(id)) {
    text = t2;
    return cast(Object) cd;
  } else return null;
}
mixin DefaultParser!(gotNamedCond, "cond.named", "75");

import ast.vardecl;
class CondExpr : Expr {
  Cond cd;
  this(Cond cd) { this.cd = cd; }
  mixin defaultIterate!(cd);
  override {
    IType valueType() { return Single!(SysInt); }
    CondExpr dup() { return new CondExpr(cd.dup); }
    void emitAsm(AsmFile af) {
      mkVar(af, Single!(SysInt), true, (Variable var) {
        iparse!(Statement, "cond_expr_ifstmt", "tree.stmt")
              (`if !cond var = false; else var = true; `,
                "cond", cd, "var", var).emitAsm(af);
      });
    }
  }
}

Object gotCondAsExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (t2.accept("eval") && rest(t2, "cond", &cd)) {
    if (cast(ExprWrap) cd) return null;
    text = t2;
    return new CondExpr(cd);
  } else return null;
}
mixin DefaultParser!(gotCondAsExpr, "tree.expr.eval_cond", "2701");
