module ast.constant;

import ast.base, ast.pointer;

class Constant : Expr {
  string name;
  this(string name) { this.name = name; }
  mixin defaultIterate!();
  override IType valueType() { return Single!(Pointer, Single!(Void)); }
  override void emitAsm(AsmFile af) {
    af.pushStack("$"~name, valueType());
  }
}
