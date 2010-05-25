module ast.ifstmt;

import ast.base, ast.scopes, ast.cond, ast.parse;

class IfStatement : Statement {
  Scope branch1, branch2;
  Cond test;
  override void emitAsm(AsmFile af) {
    test.emitAsm(af);
    auto past1 = af.genLabel();
    if (branch2) {
      test.jumpFalse(af, branch2.entry());
    } else {
      test.jumpFalse(af, past1);
    }
    branch1.emitAsm(af);
    if (!branch2) af.emitLabel(past1);
    else {
      auto past2 = af.genLabel();
      af.put("jmp ", past2);
      branch2.emitAsm(af);
      af.emitLabel(past2);
    }
  }
}

Object gotIfStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, t3;
  IfStatement ifs;
  if (t2.accept("if ") && (New(ifs), true) &&
      rest(t2, "tree.cond", &ifs.test) && rest(t2, "tree.scope", &ifs.branch1) && (
        ((t3 = t2, true) && t3.accept("else") && rest(t3, "tree.scope", &ifs.branch2) && (t2 = t3, true))
        || true
      )
    ) { text = t2; return ifs; }
  else return null;
}
mixin DefaultParser!(gotIfStmt, "tree.stmt.if");
