module ast.expr_statement;

import ast.base, ast.parse, ast.fold, ast.fun, ast.assign, ast.scopes, ast.vardecl, ast.namespace;

bool showsAnySignOfHaving(Expr ex, string thing) {
  auto it = ex.valueType();
  if (Single!(Void) == it) return false;
  if (auto ns = fastcast!(Namespace) (it)) {
    if (ns.lookup(thing)) return true;
  }
  RelNamespace rns;
  if (auto srns = fastcast!(SemiRelNamespace) (it)) rns = srns.resolve();
  if (!rns) rns = fastcast!(RelNamespace) (it);
  if (rns && rns.lookupRel(thing, ex)) return true;
  return false;
}

import ast.dg;
Object gotExprAsStmt(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t0 = text;
  if (!rest(text, "tree.expr"[], &ex)) return null;
  ex = foldex(ex);
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
  if (fastcast!(Delegate) (ex.valueType()))
    t0.failparse("discarding delegate without calling");
  return fastalloc!(ExprStatement)(ex);
}
mixin DefaultParser!(gotExprAsStmt, "tree.semicol_stmt.expr"[], "2"[]);
