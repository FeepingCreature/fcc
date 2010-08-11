module ast.parse;

import ast.base, tools.threads;
import tools.base: min, swap, apply, New, slice, stuple;
public import parseBase;

Object gotToplevel(ref string text, ParseCb cont, ParseCb rest) {
  if (auto res = rest(text, "tree.fundef")) return res;
  if (auto res = rest(text, "tree.typedef")) return res;
  if (auto res = rest(text, "tree.import")) return res;
  return null;
}
mixin DefaultParser!(gotToplevel, "tree.toplevel");

TLS!(Object) _lhs_partial;
static this() { New(_lhs_partial, { return cast(Object) null; }); }

struct lhs_partial {
  static Object using(T)(Object delegate(T) dg) {
    if (!_lhs_partial()) return null;
    if (auto c = cast(T) _lhs_partial()) {
      auto backup = c;
      scope(exit) _lhs_partial.set(cast(Object) backup);
      _lhs_partial.set(null);
      return dg(c);
    } else return null;
  }
  static Object opCall() { return _lhs_partial(); }
  static void set(T)(T t) { _lhs_partial.set(t); }
}

static this() {
  globalStateMatchers ~= matchrule("tree.rhs_partial");
}

import tools.log;
Object gotProperties(ref string text, ParseCb cont, ParseCb rest) {
  // check all possible continuations
  string longest; Object res;
  cont(text, (Object sup) {
    auto backup = lhs_partial();
    scope(exit) lhs_partial.set(backup);
    
    lhs_partial.set(sup);
    auto t2 = text;
    
    bool matched;
    while (true) {
      if (auto nl = rest(t2, "tree.rhs_partial")) {
        matched = true;
        lhs_partial.set(nl);
      } else break;
    }
    
    if (matched) {
      if (t2.ptr > longest.ptr) {
        longest = t2;
        res = lhs_partial();
      }
      return ParseCtl.AcceptCont;
    } else return ParseCtl.RejectCont;
  });
  if (longest) text = longest;
  return res;
}
mixin DefaultParser!(gotProperties, "tree.expr.properties", "3");

Object gotBraceExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (t2.accept("(") &&
      rest(t2, "tree.expr", &ex) &&
      t2.accept(")")
    ) {
    text = t2;
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces", "6");

class ExprStatement : Statement {
  Expr ex;
  this(Expr ex) { this.ex = ex; }
  mixin defaultIterate!(ex);
  override void emitAsm(AsmFile af) {
    auto cs = af.checkptStack();
    scope(exit) af.restoreCheckptStack(cs);
    ex.emitAsm(af);
  }
}

Object gotExprAsStmt(ref string text, ParseCb cont, ParseCb rest) {
  // TODO: break expr/statement inheritance. it's silly.
  Expr ex;
  auto t2 = text;
  if (rest(t2, "tree.expr", &ex)) {
    text = t2;
    return new ExprStatement(ex);
  } else return null;
}
mixin DefaultParser!(gotExprAsStmt, "tree.semicol_stmt.expr");

Object gotSemicolStmt(ref string text, ParseCb cont, ParseCb rest) {
  if (auto obj = rest(text, "tree.semicol_stmt")) {
    text.mustAccept(";", "Missing terminating semicolon at '"~text.next_text()~"'");
    return obj;
  } else return null;
}
mixin DefaultParser!(gotSemicolStmt, "tree.stmt.semicolonized");
