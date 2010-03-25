module ast.aggregate;

import ast.base;

class AggrStatement : Statement {
  Statement[] stmts;
  override void emitAsm(AsmFile af) {
    foreach (stmt; stmts)
      stmt.emitAsm(af);
  }
}
