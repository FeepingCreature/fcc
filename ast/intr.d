module ast.intr;

import ast.base, ast.int_literal;

class Interrupt : Statement {
  int which;
  this(int i) { which = i; }
  Interrupt dup() { return this; }
  override void emitLLVM(LLVMFile lf) {
    put(lf, `call void asm sideeffect "int $$`, which, `", ""()`);
  }
  mixin defaultIterate!();
}

Object gotIntrStmt(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr"[], &ex))
    throw new Exception("Couldn't match interrupt number! "[]);
  auto ie = fastcast!(IntExpr)~ ex;
  if (!ie)
    throw new Exception("Interrupt number must be a literal constant! "[]);
  return fastalloc!(Interrupt)(ie.num);
}
mixin DefaultParser!(gotIntrStmt, "tree.semicol_stmt.intr", "24", "_interrupt");
