module ast.constant;

import ast.base, ast.pointer;

class Constant : Expr {
  string name;
  this(string name) { this.name = name; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override IType valueType() { return voidp; }
  override void emitAsm(AsmFile af) {
    af.mmove4(af.addressof(name), af.regs[0]);
    af.pushStack(af.regs[0], nativePtrSize);
  }
}
