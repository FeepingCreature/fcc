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

bool haveIndentConflict(string s1, string s2) {
  void seekBackToNewline(ref string s) {
    // this is somewhat hax. Sorry.
    void stepBack() { s = (s.ptr - 1)[0 .. s.length + 1]; }
    stepBack; 
    while (s[0] != '\n') stepBack;
    s = s[1..$];
  }
  // advance s by eating spaces until matches cmp
  bool isFirstOnLine(string s, string cmp, out int spaces) {
    while (s[0] == ' ') { s = s[1 .. $]; spaces ++; }
    return s.ptr is cmp.ptr;
  }
  auto s1back = s1, s2back = s2;
  seekBackToNewline(s1back); seekBackToNewline(s2back);
  int s1dist, s2dist;
  if (!isFirstOnLine(s1back, s1, s1dist)) return false; // check that string2 is on separate line
  if (!isFirstOnLine(s2back, s2, s2dist)) return false; // check that string2 is on separate line
  return s1dist != s2dist;
}

// very hacky function! use with care!
string retreat(string s, int i) {
  return (s.ptr - i)[0..s.length + i];
}

import ast.namespace;
Object gotIfStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto pos1 = text.retreat(2);
  string t2 = text;
  auto ifs = new IfStatement;
  auto sc = new Scope; // wrapper scope
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  if (!rest(t2, "cond", &ifs.test))
    t2.failparse("Couldn't get if condition");
  configure(ifs.test);
  if (!rest(t2, "tree.scope", &ifs.branch1))
    t2.failparse("Couldn't get if branch");
  if (t2.accept("else")) {
    auto t3 = t2.retreat(4);
    if (haveIndentConflict(pos1, t3)) {
      t3.failparse("Else must be on same indentation level as opening if! ");
    }
    if (!rest(t2, "tree.scope", &ifs.branch2))
      t2.failparse("Couldn't get else branch");
  }
  text = t2;
  if (!sc._body) return ifs;
  sc.addStatement(ifs);
  return sc;
}
mixin DefaultParser!(gotIfStmt, "tree.stmt.if", "19", "if");
