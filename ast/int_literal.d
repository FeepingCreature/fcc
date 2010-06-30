module ast.int_literal;

import ast.base;

class IntExpr : Expr {
  int num;
  override {
    void emitAsm(AsmFile af) {
      af.pushStack(Format("$", num), valueType());
    }
    IType valueType() { return Single!(SysInt); }
    string toString() { return Format(num); }
  }
  this(int i) { num = i; }
  mixin defaultIterate!();
}

bool gotIntExpr(ref string text, out Expr ex) {
  int i;
  return text.gotInt(i) && (ex = new IntExpr(i), true);
}
