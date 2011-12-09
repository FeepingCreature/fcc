module ast.aggregate;

import ast.base;

class AggrStatement : Statement {
  Statement[] stmts;
  this(Statement[] stmts) { this.stmts = stmts; }
  this() { }
  mixin defaultIterate!(stmts);
  override void emitAsm(AsmFile af) {
    foreach (i, stmt; stmts) {
      // logln("aggr @", af.currentStackDepth, " [", i, "] ", stmt, " - ", stmts);
      stmt.emitAsm(af);
    }
  }
  mixin DefaultDup!();
  string toString() { return Format(stmts); }
}
