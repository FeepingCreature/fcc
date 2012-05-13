module ast.mixins;

import ast.base, ast.parse, ast.literal_string, ast.fold, ast.casting, ast.aggregate_parse;

Object gotMixinExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr"[], &ex)) 
    t2.failparse("Couldn't match mixin string! "[]);
  auto ex2 = ex;
  if (!gotImplicitCast(ex2, (Expr ex) {
    return !!fastcast!(StringExpr) (foldex(ex));
  }))
    t2.failparse("Couldn't mixin: Not a string constant: "[], ex);
  auto se = fastcast!(StringExpr) (foldex(ex2));
  auto src = se.str;
  Object res;
  pushCache(); scope(exit) popCache();
  try {
    if (!rest(src, "tree.expr"[], &res))
      src.failparse("Couldn't parse mixin string for expr"[]);
    if (src.mystripl().length)
      src.failparse("Unknown text found for expr. "[]);
  } catch (Exception ex) {
    t2.failparse("Executing mixin: "[], ex);
  }
  text = t2;
  return res;
}
mixin DefaultParser!(gotMixinExpr, "tree.expr.mixin"[], "222"[], "mixin"[]);

Object gotMixinStmt(string submode)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr"[], &ex)) 
    t2.failparse("Couldn't match mixin string! "[]);
  auto ex2 = ex;
  if (!gotImplicitCast(ex2, (Expr ex) {
    return !!fastcast!(StringExpr) (foldex(ex));
  }))
    t2.failparse("Couldn't mixin: Not a string constant: "[], ex);
  auto se = fastcast!(StringExpr) (foldex(ex2));
  auto src = se.str;
  Object res;
  pushCache(); scope(exit) popCache();
  try {
    static if (submode == "tree.stmt") {
      res = src.parseFullAggregateBody(rest);
    } else {
      if (!rest(src, submode, &res))
        src.failparse("Couldn't parse mixin string for stmt"[]);
      if (src.mystripl().length)
        src.failparse("Unknown text found for stmt. "[]);
      }
  } catch (Exception ex) {
    t2.failparse("Executing mixin '"[], src.nextText(), "': "[], ex);
  }
  static if (submode != "tree.stmt") {
    if (!t2.accept(";"))
      t2.failparse("semicolon expected");
  }
  text = t2;
  return res;
}
mixin DefaultParser!(gotMixinStmt!("tree.stmt"), "tree.semicol_stmt.mixin", "100", "mixin");
mixin DefaultParser!(gotMixinStmt!("tree.toplevel"), "tree.toplevel.mixin",  null, "mixin");
mixin DefaultParser!(gotMixinStmt!("struct_member"), "struct_member.mixin",  null, "mixin");
