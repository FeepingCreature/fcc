module ast.parse;

import ast.base, tools.threads;
import tools.base: min, swap, apply, New, slice, startsWith, stuple;
public import parseBase;

Object gotToplevel(ref string text, ParseCb cont, ParseCb rest) {
  if (auto res = rest(text, "tree.fundef")) return res;
  if (auto res = rest(text, "tree.typedef")) return res;
  if (auto res = rest(text, "tree.import")) return res;
  return null;
}
mixin DefaultParser!(gotToplevel, "tree.toplevel");

TLS!(Object) lhs_partial;
static this() { New(lhs_partial, { return cast(Object) null; }); }

Object gotProperties(ref string text, ParseCb cont, ParseCb rest) {
  auto sup = cont(text);
  if (!sup) return null;
  
  auto backup = lhs_partial();
  scope(exit) lhs_partial.set(backup);
  
  lhs_partial.set(sup);
  while (true) {
    if (auto nl = rest(text, "tree.rhs_partial")) {
      lhs_partial.set(nl);
    } else break;
  }
  return lhs_partial();
}
mixin DefaultParser!(gotProperties, "tree.expr.properties", "3");

Object gotBraceExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (text.accept("(") &&
      rest(text, "tree.expr", &ex)
    ) {
    text.mustAccept(")", Format("Missing closing brace at ", text.next_text()));
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces", "6");

Object gotExprAsStmt(ref string text, ParseCb cont, ParseCb rest) {
  // TODO: break expr/statement inheritance. it's silly.
  Expr ex;
  auto t2 = text;
  if (rest(t2, "tree.expr", &ex)) {
    text = t2;
    return cast(Object) ex;
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
