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

import tools.log;
class ForStatement : Statement {
  VarDecl decl;
  Cond cond;
  Statement step;
  Scope _body;
  override void emitAsm(AsmFile af) {
    auto backup = af.checkptStack();
    decl.emitAsm(af);
    auto start = af.genLabel(), done = af.genLabel();
    logln("for start is ", start, ", done is ", done);
    af.emitLabel(start);
    cond.emitAsm(af);
    cond.jumpFalse(af, done);
    _body.emitAsm(af);
    step.emitAsm(af);
    af.put("jmp ", start);
    af.emitLabel(done);
  }
}
