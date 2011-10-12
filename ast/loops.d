module ast.loops;

import ast.base, ast.scopes, ast.vardecl, ast.conditionals, ast.parse;
import ast.iterator, ast.int_literal, ast.fold, ast.tuples, ast.tuple_access;

// TODO: come up with a way to emit guards for a jump. this is necessary for continue/break to work correctly.

class WhileStatement : Statement {
  Scope _body;
  Cond cond;
  Scope sup;
  override WhileStatement dup() {
    auto res = new WhileStatement;
    res._body = _body.dup;
    res.cond = cond.dup;
    res.sup = sup; // goes upwards - don't dup!
    return res;
  }
  mixin defaultIterate!(cond, _body);
  override void emitAsm(AsmFile af) {
    auto start = af.genLabel(), done = af.genLabel();
    af.emitLabel(start, !keepRegs, !isForward);
    cond.jumpOn(af, false, done);
    _body.emitAsm(af);
    // TODO: rerun cond? check complexity?
    af.jump(start);
    af.emitLabel(done, !keepRegs, isForward);
  }
  override string toString() { return Format("while(", cond, ") { ", _body._body, "}"); }
}

import ast.aggregate;
Object gotWhileStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool isStatic;
  if (t2.accept("static")) isStatic = true;
  bool forMode;
  if (!t2.accept("while")) {
    if (!t2.accept("for"))
      return null;
    forMode = true;
    assert(!isStatic);
  }
  auto ws = new WhileStatement;
  auto sc = new Scope;
  sc.configPosition (t2);
  ws.sup = sc;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  if (!rest(t2, "cond", &ws.cond)) {
    if (forMode) return null;
    t2.failparse("Couldn't parse while cond");
  }
  configure(ws.cond);
  if (isStatic) {
    auto aggr = fastcast!(AggrStatement)(sc._body);
    if (!aggr) fail(Format("Malformed static while: ", sc._body));
    if (!fastcast!(VarDecl) (aggr.stmts[0]))
      fail(Format("Malformed static while (2): ", aggr.stmts));
    aggr.stmts = null; // remove loop variable declaration/s
    
    auto backupfield = sc.field;
    Expr iter_expr;
    if (auto ilc = fastcast!(IterLetCond!(LValue)) (ws.cond)) iter_expr = ilc.iter;
    if (auto imc = fastcast!(IterLetCond!(MValue)) (ws.cond)) iter_expr = imc.iter;
    if (!iter_expr) fail("Could not interpret static-loop expression");
    
    auto iter = fastcast!(RichIterator) (iter_expr.valueType());
    if (!iter) fail("static-loop expression not an iteratr! ");
    
    auto len = fastcast!(IntExpr)~ foldex(iter.length(iter_expr));
    // logln("foldex length is ", foldex(iter.length(iter_expr)));
    if (!len) fail("static-loop iterator length is not constant int! ");
    string t3;
    for (int i = 0; i < len.num; ++i) {
      auto ival = iter.index(iter_expr, mkInt(i));
      string t4 = t2;
      sc.field = backupfield.dup;
      foreach (ref entry; sc.field) {
        if (auto v = fastcast!(Variable)~ entry._1) {
          if (v.name) {
            // will be substituted with actual value in optimizer
            entry = stuple(v.name, fastcast!(Object) (ival));
          }
        }
      }
      sc.rebuildCache;
      pushCache; // same code is parsed multiple times - do not cache!
      Scope sc2;
      if (!rest(t4, "tree.scope", &sc2)) {
        t4.failparse("Couldn't parse during static-while expansion! ");
      }
      popCache;
      if (!t3) t3 = t4;
      else assert(t3 is t4);
      sc.field = backupfield;
      sc.addStatement(sc2);
    }
    t2 = t3;
  } else {
    if (!rest(t2, "tree.scope", &ws._body)) {
      if (forMode) return null;
      t2.failparse("Couldn't parse while body");
    }
    sc.addStatement(ws);
  }
  text = t2;
  sc.rebuildCache;
  return sc;
}
mixin DefaultParser!(gotWhileStmt, "tree.stmt.while", "141");

import tools.log;
class ForStatement : Statement {
  VarDecl decl;
  Cond cond;
  Statement step;
  Scope _body;
  mixin DefaultDup!();
  mixin defaultIterate!(decl, cond, step, _body);
  override void emitAsm(AsmFile af) {
    auto backup = af.checkptStack();
    scope(exit)
      af.restoreCheckptStack(backup);
    // logln("start depth is ", af.currentStackDepth);
    decl.emitAsm(af);
    auto start = af.genLabel(), done = af.genLabel();
    af.emitLabel(start, !keepRegs, !isForward);
    cond.jumpOn(af, false, done);
    _body.emitAsm(af);
    step.emitAsm(af);
    af.jump(start);
    af.emitLabel(done, !keepRegs, isForward);
  }
}

import ast.namespace;
Object gotForStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto fs = new ForStatement, check = namespace().getCheckpt();
  if (rest(t2, "tree.stmt.vardecl", &fs.decl) &&
      rest(t2, "cond", &fs.cond) && (configure(fs.cond), true) && t2.accept(";") &&
      rest(t2, "tree.semicol_stmt", &fs.step) && t2.accept(")") &&
      rest(t2, "tree.scope", &fs._body)
    )
  {
    text = t2;
    namespace().setCheckpt(check);
    return fs;
  } else t2.failparse("Failed to parse for statement");
}
mixin DefaultParser!(gotForStmt, "tree.stmt.for", "142", "for (");

class DoWhileExt : Statement {
  Scope first, second;
  Cond cond;
  mixin DefaultDup!();
  mixin defaultIterate!(first, second, cond);
  override void emitAsm(AsmFile af) {
    mixin(mustOffset("0"));
    first.needEntryLabel = true;
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
  auto dw = new DoWhileExt;
  
  auto sc = new Scope;
  sc.configPosition(t2);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  if (!rest(t2, "tree.scope", &dw.first))
    t2.failparse("Couldn't parse scope after do");
  auto backup = namespace();
  namespace.set(dw.first);
  scope(exit) namespace.set(backup);
  if (!t2.accept("while")) return null; // not a do/while extloop
  
  // You are not expected to understand this.
  {
    namespace.set(sc);
    dw.first.sup = sc.sup;
    sc.sup = dw.first;
    scope(exit) {
      namespace.set(dw.first);
      sc.sup = dw.first.sup;
      dw.first.sup = sc;
    }
    if (!rest(t2, "cond", &dw.cond))
      t2.failparse("Could not match do/while cond");
    configure(dw.cond);
  }
  if (!rest(t2, "tree.scope", &dw.second))
    t2.failparse("do/while extended second scope not matched");
  text = t2;
  sc.addStatement(dw);
  return sc;
}
mixin DefaultParser!(gotDoWhileExtStmt, "tree.stmt.do_while_ext", "143", "do");
