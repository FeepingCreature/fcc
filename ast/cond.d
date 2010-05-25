module ast.cond;

import ast.base, ast.namespace, ast.parse, tools.base;

class ExprWrap : Cond {
  Expr ex;
  mixin This!("ex");
  override {
    void emitAsm(AsmFile af) {
      assert(ex.valueType().size == 4);
      ex.emitAsm(af);
      af.popStack("%eax", ex.valueType());
      af.compare("$0", "%eax");
    }
    void jumpFalse(AsmFile af, string dest) {
      af.jumpOn(false, true, false, dest); // jump on 0.
    }
  }
}

class Compare : Cond {
  Expr e1; bool smaller, equal, greater; Expr e2;
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
  override {
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      e2.emitAsm(af);
      e1.emitAsm(af);
      af.popStack("%ebx", e1.valueType());
      af.popStack("%eax", e2.valueType());
      af.put("cmpl %eax, %ebx");
    }
    void jumpFalse(AsmFile af, string dest) {
      af.jumpOn(!smaller, !equal, !greater, dest);
    }
  }
}

Object gotCompare(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool not, smaller, equal, greater;
  Expr ex1, ex2;
  if (rest(t2, "tree.expr", &ex1) &&
      (
        (t2.accept("!") && (not = true)),
        (t2.accept("<") && (smaller = true)),
        (t2.accept(">") && (greater = true)),
        ((not || smaller || t2.accept("=")) && t2.accept("=") && (equal = true)),
        (smaller || equal || greater)
      ) && rest(t2, "tree.expr", &ex2)
  ) {
    text = t2;
    return new Compare(ex1, not, smaller, equal, greater, ex2);
  } else return null;
}
mixin DefaultParser!(gotCompare, "tree.cond.compare", "1");

import ast.literals;
Object gotExprAsCond(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (rest(text, "<tree.expr >tree.expr.cond", &ex)) {
    return new Compare(ex, true, false, true, false, new IntExpr(0));
  } else return null;
}
mixin DefaultParser!(gotExprAsCond, "tree.cond.expr", "9");
