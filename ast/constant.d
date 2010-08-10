module ast.constant;

import ast.base, ast.pointer;

class Constant : Expr {
  string name;
  this(string name) { this.name = name; }
  mixin defaultIterate!();
  override IType valueType() { return voidp; }
  override void emitAsm(AsmFile af) {
    af.pushStack("$"~name, valueType());
  }
}
