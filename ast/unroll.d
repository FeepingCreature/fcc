module ast.unroll;

import ast.base, ast.loops, ast.iterator, ast.casting, ast.fold,
  ast.int_literal, ast.scopes, ast.namespace;

import tools.log: log;

static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto ws = cast(WhileStatement) it;
    if (!ws || !ws.isStatic) return null;
    if (auto ilc = cast(IterLetCond!(LValue)) ws.cond) {
      auto iter = cast(RichIterator) ilc.iter.valueType();
      if (iter) {
        auto len = cast(IntExpr) foldex(iter.length(ilc.iter));
        if (!len) return null;
        auto backup = namespace();
        scope(exit) namespace.set(backup);
        namespace.set(ws.sup);
        auto sc = new Scope;
        for (int i = 0; i < len.num; ++i) {
          auto ival = iter.index(ilc.iter, new IntExpr(i));
          assert(ws.holders.length == 1);
          auto ph = ws.holders[0];
          int depth;
          void subst(ref Iterable it) {
            if (it is ph) {
              // logln(i, ": subst with ", ival);
              it = cast(Iterable) ival;
            }
            else it.iterate(&subst);
          }
          auto sc2 = ws._body.dup;
          sc2.iterate(&subst);
          opt(sc2);
          sc.addStatement(sc2);
        }
        return sc;
      }
    }
    return null;
  };
}
