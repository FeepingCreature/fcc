module ast.aggregate;

import ast.base;

class AggrStatement : Statement {
  Statement[] stmts;
  mixin defaultIterate!(stmts);
  override void emitAsm(AsmFile af) {
    foreach (stmt; stmts)
      stmt.emitAsm(af);
  }
  mixin DefaultDup!();
  string toString() { return Format(stmts); }
}
