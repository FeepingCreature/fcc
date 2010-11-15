module ast.ifstmt;

import ast.base, ast.scopes, ast.conditionals, ast.parse;

class IfStatement : Statement {
  Scope branch1, branch2;
  Cond test;
  mixin DefaultDup!();
  mixin defaultIterate!(test, branch1, branch2);
  override void emitAsm(AsmFile af) {
    auto past1 = af.genLabel();
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
  }
}

import ast.namespace;
Object gotIfStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, t3;
  IfStatement ifs;
  if (t2.accept("if ")) {
    New(ifs);
    {
      auto sc = new Scope; // wrapper scope of first body
      namespace.set(sc);
      scope(exit) namespace.set(sc.sup);
      ifs.branch1 = sc;
      if (!rest(t2, "cond", &ifs.test))
        t2.failparse("Couldn't get if condition");
      configure(ifs.test);
      if (!rest(t2, "tree.scope", (Statement st) { sc.addStatement(st); }))
        t2.failparse("Couldn't get if branch");
    }
    if (t2.accept("else")) {
      if (!rest(t2, "tree.scope", &ifs.branch2))
        t2.failparse("Couldn't get else branch");
    }
    text = t2;
    return ifs;
  } else return null;
}
mixin DefaultParser!(gotIfStmt, "tree.stmt.if", "19");
