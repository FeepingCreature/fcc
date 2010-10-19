module ast.intr;

import ast.base, ast.int_literal;

class Interrupt : Statement {
  int which;
  this(int i) { which = i; }
  Interrupt dup() { return this; }
  override void emitAsm(AsmFile af) { af.put("int $", which); }
  mixin defaultIterate!();
}

Object gotIntrStmt(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("_interrupt")) return null;
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    throw new Exception("Couldn't match interrupt number! ");
  auto ie = cast(IntExpr) ex;
  if (!ie)
    throw new Exception("Interrupt number must be a literal constant! ");
  return new Interrupt(ie.num);
}
mixin DefaultParser!(gotIntrStmt, "tree.semicol_stmt.intr", "31");
