module ast.fold;

import ast.base, tools.base: and;

Itr fold(Itr i) {
  if (!i) return null;
  auto cur = i;
  while (true) {
    auto start = cur;
    Expr e1;
    debug
      e1 = fastcast!(Expr)~ start;
    foreach (dg; foldopt) {
      auto backup = cur;
      if (auto res = dg(cur)) cur = res;
      debug {
        auto e2 = fastcast!(Expr)~ cur;
        if (e1 && e2 && e1.valueType() != e2.valueType()) {
          logln("Fold has violated type consistency: "[], start, " => "[], cur);
          logln("I will now run the dg again so you can step into it");
          asm { int 3; }
          dg(backup);
        }
      }
    }
    if (cur is start) break;
  }
  return cur;
}

Expr foldex(Expr ex) {
  if (!ex) return null;
  auto itr = fastcast!(Itr) (ex);
  itr = fold(itr);
  ex = fastcast!(Expr) (itr);
  return ex;
}

Statement optst(Statement st) {
  if (!st) return null;
  opt(st);
  return st;
}

void opt(T)(ref T t) {
  void fun(ref Itr it) {
    it = fold(it);
    it.iterate(&fun);
  }
  Itr it = fastcast!(Itr) (t);
  if (!it) fail;
  fun(it);
  t = fastcast!(T) (it);
  if (!t) fail;
}
