module ast.ifstmt;

import ast.base, ast.scopes, ast.testTruth;

class IfStatement : Statement {
  Scope branch1, branch2;
  Expr test;
  override void emitAsm(AsmFile af) {
    if (branch2) {
      testFalse(af, test, branch2.entry());
    } else {
      testFalse(af, test, branch1.exit());
    }
    branch1.emitAsm(af);
    if (branch2) {
      af.put("jmp ", branch2.exit());
      branch2.emitAsm(af);
    }
  }
}
