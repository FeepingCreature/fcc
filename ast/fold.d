module ast.fold;

import ast.base;

Expr fold(Expr ex) {
  Expr cur = ex;
  while (true) {
    auto start = cur;
    foreach (dg; foldopt) if (auto res = dg(cur)) cur = res;
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
