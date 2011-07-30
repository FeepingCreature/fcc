module ast.mixins;

import ast.base, ast.parse, ast.literal_string, ast.fold, ast.casting;

Object gotMixinExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex)) 
    t2.failparse("Couldn't match mixin string! ");
  auto ex2 = ex;
  if (!gotImplicitCast(ex2, (Expr ex) {
    return !!fastcast!(StringExpr) (foldex(ex));
  }))
    t2.failparse("Couldn't mixin: Not a string constant: ", ex);
  auto se = fastcast!(StringExpr) (foldex(ex2));
  auto src = se.str;
  Object res;
  pushCache(); scope(exit) popCache();
  if (!rest(src, "tree.expr", &res))
    src.failparse("Couldn't parse mixin string for expr");
  if (src.length)
    src.failparse("Unknown text found for expr. ");
  text = t2;
  return res;
}
mixin DefaultParser!(gotMixinExpr, "tree.expr.mixin", "222", "mixin");

Object gotMixinStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex)) 
    t2.failparse("Couldn't match mixin string! ");
  auto ex2 = ex;
  if (!gotImplicitCast(ex2, (Expr ex) {
    return !!fastcast!(StringExpr) (foldex(ex));
  }))
    t2.failparse("Couldn't mixin: Not a string constant: ", ex);
  auto se = fastcast!(StringExpr) (foldex(ex2));
  auto src = se.str;
  Object res;
  pushCache(); scope(exit) popCache();
  if (!rest(src, "tree.stmt", &res))
    src.failparse("Couldn't parse mixin string for stmt");
  if (src.length)
    src.failparse("Unknown text found for stmt. ");
  text = t2;
  return res;
}
mixin DefaultParser!(gotMixinStmt, "tree.semicol_stmt.mixin", "100", "mixin");
