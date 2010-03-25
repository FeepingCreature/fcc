module ast.returns;

import ast.base, ast.namespace, ast.scopes;

class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  override void emitAsm(AsmFile af) {
    auto fun = findFun(ns);
    assert(value.valueType().size == 4);
    value.emitAsm(af);
    af.mmove4("(%esp)", "%eax");
    // TODO: stack cleanup token here
    af.put("jmp ", fun._scope.exit());
  }
}
