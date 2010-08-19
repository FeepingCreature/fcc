module ast.loops;

import ast.base, ast.scopes, ast.vardecl, ast.cond, ast.parse;

class WhileStatement : Statement {
  Scope _body;
  Cond cond;
  mixin defaultIterate!(cond, _body);
  override void emitAsm(AsmFile af) {
    auto start = af.genLabel(), done = af.genLabel();
    af.emitLabel(start);
    cond.jumpOn(af, false, done);
    _body.emitAsm(af);
    // TODO: rerun cond? check complexity?
    af.jump(start);
    af.emitLabel(done);
  }
}

Object gotWhileStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("while ")) {
    auto ws = new WhileStatement;
    if (rest(t2, "cond", &ws.cond) && rest(t2, "tree.scope", &ws._body)) {
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
  mixin defaultIterate!(decl, cond, step, _body);
  override void emitAsm(AsmFile af) {
    auto backup = af.checkptStack();
    scope(exit)
      af.restoreCheckptStack(backup);
    decl.emitAsm(af);
    auto start = af.genLabel(), done = af.genLabel();
    af.emitLabel(start);
    cond.jumpOn(af, false, done);
    _body.emitAsm(af);
    step.emitAsm(af);
    af.jump(start);
    af.emitLabel(done);
  }
}

import ast.namespace;
Object gotForStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("for (")) {
    auto fs = new ForStatement, check = namespace().getCheckpt();
    if (rest(t2, "tree.stmt.vardecl", &fs.decl) &&
        rest(t2, "cond", &fs.cond) && t2.accept(";") &&
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

class DoWhileExt : Statement {
  Scope first, second;
  Cond cond;
  mixin defaultIterate!(first, second, cond);
  override void emitAsm(AsmFile af) {
    mixin(mustOffset("0"));
    auto fdg = first.open(af)(); // open and body
    auto atJump = af.checkptStack();
    cond.jumpOn(af, false, first.exit());
    second.emitAsm(af);
    fdg(true); // close before jump! variables must be cleaned up .. don't set the label though
    af.jump(first.entry());
    af.restoreCheckptStack(atJump, true);
    fdg(); // close for real
  }
}

Object gotDoWhileExtStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("do ")) {
    auto dw = new DoWhileExt;
    if (!rest(t2, "tree.scope", &dw.first)) throw new Exception("Couldn't parse scope after do at "~t2.next_text());
    auto backup = namespace();
    namespace.set(dw.first);
    scope(exit) namespace.set(backup);
    if (!t2.accept("while")) return null; // not a do/while extloop
    if (!rest(t2, "cond", &dw.cond)) throw new Exception("Could not match do/while cond at "~t2.next_text());
    if (!rest(t2, "tree.scope", &dw.second))
      throw new Exception("do/while extended second scope not matched at "~t2.next_text());
    text = t2;
    return dw;
  } else return null;
}
mixin DefaultParser!(gotDoWhileExtStmt, "tree.stmt.do_while_ext");
