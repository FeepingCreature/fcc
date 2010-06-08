module ast.int_literal;

import ast.base;

class IntExpr : Expr {
  int num;
  override void emitAsm(AsmFile af) {
    af.pushStack(Format("$", num), valueType());
  }
  override Type valueType() { return Single!(SysInt); }
  this(int i) { num = i; }
}

bool gotIntExpr(ref string text, out Expr ex) {
  int i;
  return text.gotInt(i) && (ex = new IntExpr(i), true);
}
