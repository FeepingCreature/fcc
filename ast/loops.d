module ast.loops;

import ast.base, ast.scopes, ast.variable, ast.cond, ast.parse;

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

Object gotWhileStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("while ")) {
    auto ws = new WhileStatement;
    if (rest(t2, "tree.cond", &ws.cond) && rest(t2, "tree.scope", &ws._body)) {
      text = t2;
      return ws;
    } else throw new Exception("Couldn't parse while loop at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotWhileStmt, "tree.stmt.while");

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

import ast.namespace;
Object gotForStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("for (")) {
    auto fs = new ForStatement, check = namespace().getCheckpt();
    if (rest(t2, "tree.stmt.vardecl", &fs.decl) &&
        rest(t2, "tree.cond", &fs.cond) && t2.accept(";") &&
        rest(t2, "tree.semicol_stmt", &fs.step) && t2.accept(")") &&
        rest(t2, "tree.scope", &fs._body)
      )
    {
      text = t2;
      namespace().setCheckpt(check);
      return fs;
    } else throw new Exception("Failed to parse for statement at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotForStmt, "tree.stmt.for");
