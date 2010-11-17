module ast.ifstmt;

import ast.base, ast.scopes, ast.conditionals, ast.parse;

class IfStatement : Statement {
  Scope wrapper, branch1, branch2;
  Cond test;
  mixin DefaultDup!();
  mixin defaultIterate!(test, branch1, branch2);
  override void emitAsm(AsmFile af) {
    auto past1 = af.genLabel();
    auto close = wrapper.open(af)(); // cond needs scope open and willing
    if (branch2) {
      test.jumpOn(af, false, branch2.entry());
    } else {
      test.jumpOn(af, false, past1);
    }
    branch1.emitAsm(af);
    if (!branch2) af.emitLabel(past1);
    else {
      auto past2 = af.genLabel();
      af.jump(past2);
      branch2.emitAsm(af);
      af.emitLabel(past2);
    }
    close();
  }
}

import ast.namespace;
Object gotIfStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, t3;
  auto ifs = new IfStatement;
  {
    auto sc = new Scope; // wrapper scope of first body
    namespace.set(sc);
    scope(exit) namespace.set(sc.sup);
    ifs.wrapper = sc;
    if (!rest(t2, "cond", &ifs.test))
      t2.failparse("Couldn't get if condition");
    configure(ifs.test);
    if (!rest(t2, "tree.scope", &ifs.branch1))
      t2.failparse("Couldn't get if branch");
  }
  if (t2.accept("else")) {
    if (!rest(t2, "tree.scope", &ifs.branch2))
      t2.failparse("Couldn't get else branch");
  }
  text = t2;
  return ifs;
}
mixin DefaultParser!(gotIfStmt, "tree.stmt.if", "19", "if");
