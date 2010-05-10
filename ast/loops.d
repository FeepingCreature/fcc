module ast.loops;

import ast.base, ast.scopes, ast.testTruth;

class WhileStatement : Statement {
  Scope _body;
  Expr cond;
  override void emitAsm(AsmFile af) {
    assert(cond.valueType().size == 4);
    auto test = af.genLabel();
    testFalse(af, cond, _body.exit());
    _body.emitAsm(af);
    // TODO: rerun cond? check complexity?
    af.put("jmp ", test);
  }
}
