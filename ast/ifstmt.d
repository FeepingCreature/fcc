module ast.ifstmt;

import ast.base, ast.scopes, ast.conditionals, ast.parse, ast.properties;

class IfStatement : LineNumberedStatementClass {
  Scope wrapper;
  Statement branch1, branch2;
  Cond test;
  mixin DefaultDup!();
  mixin defaultIterate!(test, wrapper, branch1, branch2);
  string toString() { return Format("if "[], test, " "[], branch1, " else "[], branch2); }
  this() { }
  override void emitLLVM(LLVMFile lf) {
    super.emitLLVM(lf);
    auto past1 = lf.allocLabel(), past2 = lf.allocLabel();
    auto dg = wrapper.open(lf)();
      test.jumpOn(lf, false, past1);
      branch1.emitLLVM(lf);
      if (branch2) { dg(true); jump(lf, past2); }
      lf.emitLabel(past1, true);
    dg(false);
    
    if (branch2) {
      branch2.emitLLVM(lf);
      lf.emitLabel(past2, true);
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
  auto ifs = fastalloc!(IfStatement)();
  ifs.configPosition(text);
  ifs.wrapper = fastalloc!(Scope)();
  namespace.set(ifs.wrapper);
  
  {
    auto backup = *propcfg.ptr();
    scope(exit) *propcfg.ptr() = backup;
    // if (foo) bar == if (foo) { bar; }, not if (foo bar)!
    // don't try to interpret as a call if our prop starts with an ast tuple
    propcfg.ptr().withCallOnTuple = false;
    
    if (!rest(t2, "cond"[], &ifs.test))
      t2.failparse("Couldn't get if condition"[]);
  }
  configure(ifs.test);
  if (!rest(t2, "tree.scope"[], &ifs.branch1))
    t2.failparse("Couldn't get if branch"[]);
  namespace.set(ifs.wrapper.sup); // else is OUTSIDE the wrapper!
  if (t2.accept("else"[])) {
    auto t3 = t2.retreat(4);
    if (haveIndentConflict(pos1, t3)) {
      t3.failparse("Else must be on same indentation level as opening if! "[]);
    }
    if (!rest(t2, "tree.scope"[], &ifs.branch2))
      t2.failparse("Couldn't get else branch"[]);
  }
  text = t2;
  return ifs;
}
mixin DefaultParser!(gotIfStmt, "tree.stmt.if"[], "19"[], "if"[]);

import ast.fold, ast.stringparse, ast.aggregate_parse, ast.platform, ast.structure;
Object gotStaticIf(int Mode)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond test;
  if (!rest(t2, "cond"[], &test))
    t2.failparse("Couldn't get static-if condition"[]);
  string branch1, branch2;
  t2.noMoreHeredoc();
  opt(test);
  
  auto t3 = t2;
  
  branch1 = t3.coarseLexScope(true, false);
  
  if (t3.accept("else"[]))
    branch2 = t3.coarseLexScope(true, false);
  
  Statement res;
  
  auto popCache = pushCache(); scope(exit) popCache();
  
  if (isStaticTrue(test)) {
    static if (Mode == 2) { res = branch1.parseFullAggregateBody(rest); }
    else static if (Mode == 1) {
      matchStructBodySegment(branch1, namespace(), &rest, false, true);
      res = Single!(NoOp);
    } else { res = branch1.parseGlobalBody(rest, false); }
  } else if (isStaticFalse(test)) {
    if (branch2) {
      static if (Mode == 2) { res = branch2.parseFullAggregateBody(rest); }
      else static if (Mode == 1) {
        matchStructBodySegment(branch2, namespace(), &rest, false, true);
        res = Single!(NoOp);
      } else { res = branch2.parseGlobalBody(rest, false); }
    } else {
      res = Single!(NoOp);
    }
  } else {
    text.failparse("condition not static: "[], test);
  }
  
  text = t3;
  return fastcast!(Object) (res);
}
mixin DefaultParser!(gotStaticIf!(0), "tree.toplevel.a_static_if", null, "static if"); // sort first because is also cheap to exclude
mixin DefaultParser!(gotStaticIf!(1), "struct_member.a_static_if", null, "static if");
mixin DefaultParser!(gotStaticIf!(2) , "tree.stmt.static_if", "190", "static if");
