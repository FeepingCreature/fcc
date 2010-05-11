module ast.cond;

import ast.base, ast.namespace, tools.base;

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
