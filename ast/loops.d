module ast.loops;

import ast.base, ast.scopes, ast.variable, ast.cond;

class WhileStatement : Statement {
  Scope _body;
  Cond cond;
  override void emitAsm(AsmFile af) {
    auto start = af.genLabel(), done = af.genLabel();
    af.emitLabel(start);
    cond.emitAsm(af);
    cond.jumpFalse(af, done);
    _body.emitAsm(af);
    // TODO: rerun cond? check complexity?
    af.put("jmp ", start);
    af.emitLabel(done);
  }
}
