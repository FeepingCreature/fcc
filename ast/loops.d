module ast.loops;

import ast.base, ast.scopes, ast.vardecl, ast.conditionals, ast.parse, ast.fun;
import ast.iterator, ast.int_literal, ast.fold, ast.tuples, ast.tuple_access;

// TODO: come up with a way to emit guards for a jump. this is necessary for continue/break to work correctly.

interface Breakable {
  Stuple!(string, int) getContinueLabel();
  Stuple!(string, int) getBreakLabel();
  Statement[] getOutsideGuards(); // guards at the point of exit; ie. break
  Statement[] getInsideGuards(); // guards at the point of loop end; ie. continue
}

TLS!(Stuple!(Breakable, Function)) breakable_context;
static this() { New(breakable_context); }

template DefaultBreakableImpl() {
  string chosenContinueLabel, chosenBreakLabel;
  int continueDepth, breakDepth;
  Statement[] outsideGuards, insideGuards;
  override {
    Stuple!(string, int) getContinueLabel() { return stuple(chosenContinueLabel, continueDepth); }
    Stuple!(string, int) getBreakLabel() { return stuple(chosenBreakLabel, breakDepth); }
    Statement[] getOutsideGuards() { return outsideGuards; }
    Statement[] getInsideGuards() { return insideGuards; }
  }
}

class WhileStatement : Statement, Breakable {
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
  mixin DefaultBreakableImpl!();
  override {
    void emitAsm(AsmFile af) {
      auto start = af.genLabel(), done = af.genLabel();
      continueDepth = breakDepth = af.currentStackDepth;
      chosenContinueLabel = start;
      chosenBreakLabel = done;
      af.emitLabel(start, !keepRegs, !isForward);
      cond.jumpOn(af, false, done);
      _body.emitAsm(af);
      // TODO: rerun cond? check complexity?
      af.jump(start);
      af.emitLabel(done, !keepRegs, isForward);
    }
    string toString() { return Format("while("[], cond, "[]) { "[], _body._body, "}"[]); }
  }
}

import ast.aggregate;
Object gotWhileStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool isStatic;
  if (t2.accept("static"[])) isStatic = true;
  bool forMode;
  if (!t2.accept("while"[])) {
    if (!t2.accept("for"[]))
      return null;
    forMode = true;
    assert(!isStatic);
  }
  auto ws = new WhileStatement;
  auto sc = new Scope;
  ws.outsideGuards = sc.getGuards();
  sc.configPosition (t2);
  ws.sup = sc;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  if (!rest(t2, "cond"[], &ws.cond)) {
    if (forMode) return null;
    t2.failparse("Couldn't parse while cond"[]);
  }
  configure(ws.cond);
  ws.insideGuards = sc.getGuards();
  
  auto brbackup = *breakable_context.ptr();
  *breakable_context.ptr() = stuple(fastcast!(Breakable)(ws), sc.get!(Function));
  scope(exit) *breakable_context.ptr() = brbackup;
  
  if (isStatic) {
    auto aggr = fastcast!(AggrStatement)(sc._body);
    if (!aggr) fail(Format("Malformed static while: "[], sc._body));
    if (!fastcast!(VarDecl) (aggr.stmts[0]))
      fail(Format("Malformed static while (2): "[], aggr.stmts));
    aggr.stmts = null; // remove loop variable declaration/s
    
    auto backupfield = sc.field;
    Expr iter_expr;
    if (auto ilc = fastcast!(IterLetCond!(LValue)) (ws.cond)) iter_expr = ilc.iter;
    if (auto imc = fastcast!(IterLetCond!(MValue)) (ws.cond)) iter_expr = imc.iter;
    if (!iter_expr) fail("Could not interpret static-loop expression"[]);
    
    auto iter = fastcast!(RichIterator) (iter_expr.valueType());
    if (!iter) fail("static-loop expression not an iteratr! "[]);
    
    auto len = fastcast!(IntExpr)~ foldex(iter.length(iter_expr));
    // logln("foldex length is "[], foldex(iter.length(iter_expr)));
    if (!len) fail("static-loop iterator length is not constant int! "[]);
    string t3;
    for (int i = 0; i < len.num; ++i) {
      auto ival = foldex(iter.index(iter_expr, mkInt(i)));
      string t4 = t2;
      sc.field = backupfield.dup;
      string name;
      foreach (entry; sc.field) if (entry._0.length) if (auto v = fastcast!(Variable) (entry._1)) { name = entry._0; break; }
      sc.field.length = 0;
      sc.field ~= stuple(name, fastcast!(Object) (ival));
      sc.rebuildCache;
      pushCache; // same code is parsed multiple times - do not cache!
      scope(exit) popCache;
      Scope sc2;
      if (!rest(t4, "tree.scope"[], &sc2)) {
        t4.failparse("Couldn't parse during static-while expansion! "[]);
      }
      if (!t3) t3 = t4;
      else assert(t3 is t4);
      sc.field = backupfield;
      sc.addStatement(sc2);
    }
    t2 = t3;
  } else {
    if (!rest(t2, "tree.scope"[], &ws._body)) {
      if (forMode) return null;
      t2.failparse("Couldn't parse while body"[]);
    }
    sc.addStatement(ws);
  }
  text = t2;
  sc.rebuildCache;
  return sc;
}
mixin DefaultParser!(gotWhileStmt, "tree.stmt.while"[], "141"[]);

import tools.log;
class ForStatement : Statement, Breakable {
  Statement decl;
  Cond cond;
  Statement step;
  Scope _body;
  mixin DefaultDup!();
  mixin DefaultBreakableImpl!();
  mixin defaultIterate!(decl, cond, step, _body);
  override void emitAsm(AsmFile af) {
    auto backup = af.checkptStack();
    scope(exit)
      af.restoreCheckptStack(backup);
    
    // logln("start depth is "[], af.currentStackDepth);
    decl.emitAsm(af);
    
    continueDepth = breakDepth = af.currentStackDepth;
    
    auto start = af.genLabel(), done = af.genLabel(), cont = af.genLabel();
    chosenContinueLabel = cont;
    chosenBreakLabel = done;
    
    af.emitLabel(start, !keepRegs, !isForward);
    cond.jumpOn(af, false, done);
    _body.emitAsm(af);
    af.emitLabel(cont, !keepRegs, isForward);
    step.emitAsm(af);
    af.jump(start);
    af.emitLabel(done, !keepRegs, isForward);
  }
}

import ast.namespace;
Object gotForStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("("[])) return null;
  auto fs = new ForStatement, check = namespace().getCheckpt();
  auto sl = namespace().get!(ScopeLike);
  fs.outsideGuards = sl.getGuards();
  if (rest(t2, "tree.stmt.vardecl"[], &fs.decl) &&
      rest(t2, "cond"[], &fs.cond) && (configure(fs.cond), true) && t2.accept(";"[]) &&
      rest(t2, "tree.semicol_stmt"[], &fs.step) && t2.accept(")"[])
    )
  {
    fs.insideGuards = sl.getGuards();
    
    auto brbackup = *breakable_context.ptr();
    *breakable_context.ptr() = stuple(fastcast!(Breakable)(fs), namespace().get!(Function));
    scope(exit) *breakable_context.ptr() = brbackup;
    
    if (!rest(t2, "tree.scope"[], &fs._body))
      t2.failparse("Failed to parse 'for' body"[]);
    
    text = t2;
    namespace().setCheckpt(check);
    return fs;
  } else t2.failparse("Failed to parse 'for' statement"[]);
}
mixin DefaultParser!(gotForStmt, "tree.stmt.for"[], "142"[], "for"[]);

class DoWhileExt : Statement {
  Scope first, second;
  Cond cond;
  mixin DefaultDup!();
  mixin defaultIterate!(first, second, cond);
  override void emitAsm(AsmFile af) {
    mixin(mustOffset("0"[]));
    first.needEntryLabel = true;
    auto fdg = first.open(af)(); // open and body
    auto atJump = af.checkptStack();
    cond.jumpOn(af, false, first.exit());
    second.emitAsm(af);
    fdg(true); // close before jump! variables must be cleaned up .. don't set the label though
    af.jump(first.entry());
    af.restoreCheckptStack(atJump, true);
    fdg(false); // close for real
  }
}

Object gotDoWhileExtStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto dw = new DoWhileExt;
  
  auto sc = new Scope;
  sc.configPosition(t2);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  if (!rest(t2, "tree.scope"[], &dw.first))
    t2.failparse("Couldn't parse scope after do"[]);
  auto backup = namespace();
  namespace.set(dw.first);
  scope(exit) namespace.set(backup);
  if (!t2.accept("while"[])) return null; // not a do/while extloop
  
  if (!rest(t2, "cond"[], &dw.cond))
    t2.failparse("Could not match do/while cond"[]);
  configure(dw.cond);
  
  if (!rest(t2, "tree.scope"[], &dw.second))
    t2.failparse("do/while extended second scope not matched"[]);
  text = t2;
  sc.addStatement(dw);
  return sc;
}
mixin DefaultParser!(gotDoWhileExtStmt, "tree.stmt.do_while_ext"[], "143"[], "do"[]);

class ExecGuardsAndJump : Statement {
  Statement[] guards;
  int[] offsets;
  bool modeContinue;
  Breakable brk;
  mixin defaultIterate!();
  mixin MyThis!("guards, offsets, modeContinue, brk"[]);
  override {
    ExecGuardsAndJump dup() {
      return this; // no mutable parts, no iteration
    }
    void emitAsm(AsmFile af) {
      auto depth = af.checkptStack();
      // reset the stack so we can emit regular scope guards after us;
      // despite the utter pointlessness of cleaning up after an unconditional jump,
      // appearances must be honoured.
      // the optimizer can remove all that crud anyway.
      scope(success) af.restoreCheckptStack(depth, true);
      
      string targetlabel; int targetdepth;
      ptuple(targetlabel, targetdepth) = modeContinue?brk.getContinueLabel():brk.getBreakLabel();
      foreach_reverse (i, stmt; guards) {
        auto delta = af.currentStackDepth - offsets[i];
        if (delta) {
          af.restoreCheckptStack(offsets[i]);
        }
        // justification for dup see class ReturnStmt in ast.returns
        stmt.dup().emitAsm(af);
      }
      af.restoreCheckptStack(targetdepth);
      af.jump(targetlabel);
    }
  }
}

Object gotContinueOrBreak(bool gotContinue)(ref string text, ParseCb cont, ParseCb rest) {
  auto brc = *breakable_context.ptr();
  auto fun = namespace().get!(Function);
  if (fun !is brc._1 || !brc._0)
    text.failparse("No continue-capable context found!"[]);
  auto sl = namespace().get!(ScopeLike);
  auto guards = sl.getGuards();
  auto guards2 = gotContinue?brc._0.getInsideGuards():brc._0.getOutsideGuards();
  if (guards2.length > guards.length)
    text.failparse("Invalid guard structure: "[], guards, " vs. "[], guards2);
  foreach (i, guard; guards2)
    if (guard !is guards2[i])
      text.failparse("Invalid guard structure: "[], guards, " vs. "[], guards2, " at "[], i);
  auto gos = sl.getGuardOffsets();
  return fastalloc!(ExecGuardsAndJump)(guards[guards2.length .. $], gos[guards2.length .. $], gotContinue, brc._0);
}
mixin DefaultParser!(gotContinueOrBreak!(true), "tree.semicol_stmt.continue"[], "341"[], "continue"[]);
mixin DefaultParser!(gotContinueOrBreak!(false), "tree.semicol_stmt.break"[], "342"[], "break"[]);
