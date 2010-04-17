module ast.ifstmt;

import ast.base, ast.scopes;

class IfStatement : Statement {
  Scope branch1, branch2;
  Expr test;
  override void emitAsm(AsmFile af) {
    test.emitAsm(af);
    assert(test.valueType().size == 4);
    af.popStack("%eax", test.valueType());
    af.compare("$0", "%eax");
    if (branch2)
      af.put("je ", branch2.entry());
    else
      af.put("je ", branch1.exit());
    
    branch1.emitAsm(af);
    if (branch2) {
      af.put("jmp ", branch2.exit());
      branch2.emitAsm(af);
    }
  }
}
