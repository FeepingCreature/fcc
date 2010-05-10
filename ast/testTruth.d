module ast.testTruth;

import ast.base, ast.scopes, ast.testTruth;

void testFalse(AsmFile af, Expr cond, string then_jump) {
  assert(cond.valueType().size == 4);
  cond.emitAsm(af);
  af.popStack("%eax", cond.valueType());
  af.compare("$0", "%eax");
  af.put("je ", then_jump);
}
