module ast.fold;

import ast.base;

Expr fold(Expr ex) {
  Expr cur = ex;
  while (true) {
    auto start = cur;
    foreach (dg; opts) if (auto res = dg(cur)) cur = res;
    if (cur is start) break;
  }
  return cur;
}
