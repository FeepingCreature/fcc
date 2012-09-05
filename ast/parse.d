module ast.parse;

import ast.base, tools.threads;
import tools.base: min, swap, apply, New, slice, stuple;
public import parseBase;

Object gotToplevel(ref string text, ParseCb cont, ParseCb rest) {
  if (auto res = rest(text, "tree.fundef"[])) return res;
  if (auto res = rest(text, "tree.typedef"[])) return res;
  if (auto res = rest(text, "tree.import"[])) return res;
  return null;
}
mixin DefaultParser!(gotToplevel, "tree.toplevel"[]);

TLS!(Object) _lhs_partial;
static this() {
  New(_lhs_partial, { return cast(Object) null; });
}

struct lhs_partial {
  static Object using(T)(Object delegate(T) dg) {
    if (!_lhs_partial()) return null;
    if (auto c = fastcast!(T)~ _lhs_partial()) {
      auto backup = c;
      scope(exit) _lhs_partial.set(fastcast!(Object)~ backup);
      _lhs_partial.set(null);
      return dg(c);
    } else return null;
  }
  static Object opCall() { return _lhs_partial(); }
  static void set(T)(T t) { _lhs_partial.set(t); }
}

static this() {
  int ignore; // leak memory .. meh
  globalStateMatchers ~= matchrule("tree.rhs_partial"[], ignore);
}

class ExprStatement : LineNumberedStatementClass {
  Expr ex;
  this(Expr ex) { this.ex = ex; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override string toString() { return Format(ex); }
  override void emitAsm(AsmFile af) {
    super.emitAsm(af);
    auto cs = af.checkptStack();
    scope(success) af.restoreCheckptStack(cs);
    auto type = ex.valueType(), size = (Single!(Void) == type)?0:type.size;
    alignStackFor(type, af);
    mixin(mustOffset("size"[]));
    ex.emitAsm(af);
  }
}

Object gotSemicolStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto backup = text;
  if (auto obj = rest(text, "tree.semicol_stmt"[])) {
    // text.mustAcceptTerminatorSoft(Format("Missing semicolon to terminate "[], obj));
    text.mustAcceptTerminatorSoft("Missing semicolon to terminate statement");
    // logln("obj = "[], (cast(Object) obj).classinfo.name, ", "[], obj);
    if (auto lns = fastcast!(LineNumberedStatement) (obj))
      lns.configPosition(backup);
    return obj;
  } else return null;
}
mixin DefaultParser!(gotSemicolStmt, "tree.stmt.semicolonized"[], "5"[]);
