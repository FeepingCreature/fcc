module ast.fold;

import ast.base, tools.base: and;

Expr fold(Expr ex) {
  if (!ex) return null;
  Expr cur = ex;
  while (true) {
    auto start = cur;
    foreach (dg; foldopt) {
      if (auto res = dg(cur)) cur = res;
      // logln("TEST ", (cast(Object) cur.valueType()).classinfo.name, " != ", (cast(Object) start.valueType()).classinfo.name, ": ", cur.valueType() != start.valueType());
      if (cur.valueType() != start.valueType()) {
        throw new Exception(Format("Fold has violated type consistency: ", start, " => ", cur));
      }
    }
    if (cur is start) break;
  }
  return cur;
}

Expr opt(Expr ex) {
  ex = ex.dup;
  void fun(ref Iterable it) {
    if (auto ex = cast(Expr) it) {
      it = cast(Iterable) fold(ex);
    }
    it.iterate(&fun);
  }
  auto it = cast(Iterable) ex;
  fun(it);
  return cast(Expr) it;
}
