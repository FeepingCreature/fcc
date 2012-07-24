module ast.expr_statement;

import ast.base, ast.parse, ast.fold, ast.fun, ast.assign, ast.scopes, ast.vardecl, ast.namespace;

import ast.dg;
Object gotExprAsStmt(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t0 = text;
  if (!rest(text, "tree.expr"[], &ex)) return null;
  opt(ex);
  auto fc = fastcast!(FunCall) (ex);
  if (fc && fc.fun.reassign) {
    auto args = fc.getParams();
    auto lv = fastcast!(LValue) (args[0]), mv = fastcast!(MValue) (args[0]);
    if (!lv && !mv) {
      text.failparse("cannot call reassigning function "[], fc.fun.name, " on non-lvalue/mvalue "[], lv?fastcast!(Expr) (lv):mv);
    }
    // logln("expr as statement on "[], fc.fun);
    return fastcast!(Object) (mkAssignment(args[0], ex));
  }
  if (showsAnySignOfHaving(ex, "onDiscard")) {
    auto sc = fastalloc!(Scope)();
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(sc);
    
    auto lv = lvize(ex);
    if (auto onUsing = iparse!(Statement, "onUsing", "tree.semicol_stmt.expr", canFail)
                              ("evaluate lv.onDiscard"[], "lv"[], lv))
      sc.addStatement(onUsing);
    return sc;
  }
  if (auto dg = fastcast!(Delegate) (ex.valueType()))
    if (dg !is dg.ret)
      t0.failparse("discarding delegate without calling");
  return fastalloc!(ExprStatement)(ex);
}
mixin DefaultParser!(gotExprAsStmt, "tree.semicol_stmt.expr"[], "2"[]);
