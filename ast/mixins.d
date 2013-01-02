module ast.mixins;

import ast.base, ast.parse, ast.literal_string, ast.fold, ast.casting, ast.aggregate_parse, ast.platform, ast.aliasing, ast.namespace, ast.structure;

Object gotMixinExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr"[], &ex)) 
    t2.failparse("Couldn't match mixin string! "[]);
  auto ex2 = ex;
  if (!gotImplicitCast(ex2, (Expr ex) {
    opt(ex);
    return !!fastcast!(StringExpr) (ex);
  }))
    t2.failparse("Couldn't mixin: Not a string constant: "[], ex);
  opt(ex2);
  auto se = fastcast!(StringExpr) (ex2);
  auto src = se.str;
  Object res;
  auto popCache = pushCache(); scope(exit) popCache();
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
    opt(ex);
    return !!fastcast!(StringExpr) (ex);
  }))
    t2.failparse("Couldn't mixin: Not a string constant: "[], ex);
  static if (submode != "tree.stmt") {
    if (!t2.accept(";"))
      t2.failparse("semicolon expected");
  }
  opt(ex2);
  auto se = fastcast!(StringExpr) (ex2);
  auto src = se.str;
  if (!src.length) {
    text = t2;
    if (submode == "struct_member") return fastalloc!(ExprAlias)(fastcast!(Expr)(sysmod.lookup("null")), cast(string) null);
    return Single!(NoOp);
  }
  Object res;
  auto popCache = pushCache(); scope(exit) popCache();
  try {
    static if (submode == "tree.stmt") {
      res = Single!(NoOp);
      src.parseFullAggregateBody(rest);
    } else static if (submode == "tree.toplevel") {
      res = Single!(NoOp);
      src.parseGlobalBody(rest, false);
    } else static if (submode == "struct_member") {
      auto st = fastcast!(Namespace)(namespace().get!(StructLike)());
      if (!st) src.failparse("No struct under ", namespace());
      if (!src.matchStructBodySegment(st, &rest))
        src.failparse("Couldn't parse mixin string for struct segment");
      if (src.mystripl().length)
        src.failparse("Unknown text found for struct segment");
      res = Single!(NamedNull); // added directly
    } else {
      if (!rest(src, submode, &res))
        src.failparse("Couldn't parse mixin string for ", submode);
      if (src.mystripl().length)
        src.failparse("Unknown text found for stmt. "[]);
    }
  } catch (Exception ex) {
    t2.failparse("Executing mixin '"[], src.nextText(), "': "[], ex);
  }
  text = t2;
  return res;
}
mixin DefaultParser!(gotMixinStmt!("tree.stmt"), "tree.semicol_stmt.mixin", "100", "mixin");
mixin DefaultParser!(gotMixinStmt!("tree.toplevel"), "tree.toplevel.mixin",  null, "mixin");
mixin DefaultParser!(gotMixinStmt!("struct_member"), "struct_member.mixin",  null, "mixin");
