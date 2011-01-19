module ast.fold;

import ast.base, tools.base: and;

Itr fold(Itr i) {
  if (!i) return null;
  auto cur = i;
  while (true) {
    auto start = cur;
    Expr e1;
    debug e1 = cast(Expr) start;
    foreach (dg; foldopt) {
      if (auto res = dg(cur)) cur = res;
      // logln("TEST ", (cast(Object) cur.valueType()).classinfo.name, " != ", (cast(Object) start.valueType()).classinfo.name, ": ", cur.valueType() != start.valueType());
      debug {
        auto e2 = cast(Expr) cur;
        if (e1 && e2 && e1.valueType() != e2.valueType()) {
          throw new Exception(Format("Fold has violated type consistency: ", start, " => ", cur));
        }
      }
    }
    if (cur is start) break;
  }
  return cur;
}

Expr foldex(Expr ex) {
  if (!ex) return null;
  auto cur = ex;
  while (true) {
    auto start = cur;
    foreach (dg; _foldopt_expr) {
      if (auto res = dg(cur)) cur = res;
    }
    if (cur is start) break;
  }
  return cur;
}

Statement optst(Statement st) {
  if (!st) return null;
  opt(st);
  return st;
}

void opt(T)(ref T t) {
  void fun(ref Itr it) {
    if (auto ex = cast(Expr) it) {
      ex = foldex(ex);
      it = cast(Itr) ex;
    } else {
      it = fold(it);
    }
    it.iterate(&fun);
  }
  Itr it = cast(Itr) t;
  if (!it) asm { int 3; }
  fun(it);
  t = cast(T) it;
  assert(!!t);
}
