module ast.ifstmt;

import ast.base, ast.scopes, ast.cond;

class IfStatement : Statement {
  Scope branch1, branch2;
  Cond test;
  override void emitAsm(AsmFile af) {
    test.emitAsm(af);
    auto past1 = af.genLabel();
    if (branch2) {
      test.jumpFalse(af, branch2.entry());
    } else {
      test.jumpFalse(af, past1);
    }
    branch1.emitAsm(af);
    if (!branch2) af.emitLabel(past1);
    else {
      auto past2 = af.genLabel();
      af.put("jmp ", past2);
      branch2.emitAsm(af);
      af.emitLabel(past2);
    }
  }
}
