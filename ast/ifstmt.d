module ast.ifstmt;

import ast.base, ast.scopes, ast.cond, ast.parse;

class IfStatement : Statement {
  Scope branch1, branch2;
  Cond test;
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
      af.put("jmp ", past2);
      branch2.emitAsm(af);
      af.emitLabel(past2);
    }
  }
}

Object gotIfStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, t3;
  IfStatement ifs;
  if (t2.accept("if ")) {
    New(ifs);
    if (!rest(t2, "cond", &ifs.test))
      throw new Exception("Couldn't get if condition at "~t2.next_text());
    if (!rest(t2, "tree.scope", &ifs.branch1))
      throw new Exception("Couldn't get if branch1 at "~t2.next_text());
    if (t2.accept("else")) {
      if (!rest(t2, "tree.scope", &ifs.branch2))
        throw new Exception("Couldn't get if branch2 at "~t2.next_text());
    }
    text = t2;
    return ifs;
  } else return null;
}
mixin DefaultParser!(gotIfStmt, "tree.stmt.if");
