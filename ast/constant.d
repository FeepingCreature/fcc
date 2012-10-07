module ast.constant;

import ast.base, ast.pointer;

class Constant : Expr {
  string name;
  this(string name) { this.name = name; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override IType valueType() { return voidp; }
  override void emitLLVM(LLVMFile lf) {
    todo("Constant::emitLLVM");
    /*lf.mmove4(lf.addressof(name), lf.regs[0]);
    lf.pushStack(lf.regs[0], nativePtrSize);*/
  }
}
