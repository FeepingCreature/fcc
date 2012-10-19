module ast.aggregate;

import ast.base;

class AggrStatement : Statement {
  Statement[] stmts;
  this(Statement[] stmts) { this.stmts = stmts; }
  this() { }
  mixin defaultIterate!(stmts);
  override void emitLLVM(LLVMFile lf) {
    foreach (i, stmt; stmts) {
      // logln("aggr @", lf.currentStackDepth, " [", i+1, "/", stmts.length, "] ", stmt/*, " - ", stmts*/);
      stmt.emitLLVM(lf);
    }
  }
  mixin DefaultDup!();
  string toString() { return Format(stmts); }
}
