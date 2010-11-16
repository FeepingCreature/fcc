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
  int ignore; // leak memory .. meh
  globalStateMatchers ~= matchrule("tree.rhs_partial", ignore);
}

class ExprStatement : Statement {
  Expr ex;
  this(Expr ex) { this.ex = ex; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override string toString() { return Format(ex); }
  override void emitAsm(AsmFile af) {
    auto cs = af.checkptStack();
    scope(exit) af.restoreCheckptStack(cs);
    auto type = ex.valueType(), size = (type == Single!(Void))?0:type.size;
    mixin(mustOffset("size"));
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
mixin DefaultParser!(gotExprAsStmt, "tree.semicol_stmt.expr", "2");

Object gotSemicolStmt(ref string text, ParseCb cont, ParseCb rest) {
  if (auto obj = rest(text, "tree.semicol_stmt")) {
    text.mustAccept(";", Format("Missing semicolon to terminate ", obj));
    return obj;
  } else return null;
}
mixin DefaultParser!(gotSemicolStmt, "tree.stmt.semicolonized", "5");
