module ast.unroll;

import ast.base, ast.loops, ast.iterator, ast.casting, ast.fold,
  ast.int_literal, ast.scopes, ast.namespace, ast.tuples, ast.tuple_access;

import tools.log: log;

static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto ws = fastcast!(WhileStatement) (it);
    if (!ws || !ws.isStatic) return null;
    Expr iter_expr;
    if (auto ilc = fastcast!(IterLetCond!(LValue)) (ws.cond)) iter_expr = ilc.iter;
    if (auto imc = fastcast!(IterLetCond!(MValue)) (ws.cond)) iter_expr = imc.iter;
    if (!iter_expr) return null;
    auto iter = fastcast!(RichIterator)~ iter_expr.valueType();
    if (!iter) return null;
    
    auto len = fastcast!(IntExpr)~ foldex(iter.length(iter_expr));
    logln("foldex length is ", foldex(iter.length(iter_expr)));
    if (!len) return null;
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(ws.sup);
    auto sc = new Scope;
    for (int i = 0; i < len.num; ++i) {
      auto ival = iter.index(iter_expr, mkInt(i));
      int depth;
      void subst(ref Iterable it) {
        foreach (i, ph; ws.holders) {
          if (it is ph) {
            if (fastcast!(Tuple)~ ival.valueType()) {
              it = fastcast!(Iterable)~ getTupleEntries(ival)[i]; // assume is basic. ._.
            } else {
              assert(!i);
              it = fastcast!(Iterable)~ ival;
            }
            return;
          }
        }
        it.iterate(&subst);
      }
      auto sc2 = ws._body.dup;
      sc2.iterate(&subst);
      opt(sc2);
      sc.addStatement(sc2);
    }
    return sc;
  };
}
