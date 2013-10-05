module ast.fold;

import ast.base, tools.base: and;

Itr fold(Itr i, bool collapse) {
  if (!i) return null;
  if (collapse)
    if (auto tr = fastcast!(Tree)(i))
      i = fastcast!(Itr)(.collapse(tr));
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
          logln("from: ", (cast(Object)(e1.valueType())).classinfo.name, " ", e1.valueType());
          logln("to: ", (cast(Object)(e2.valueType())).classinfo.name, " ", e2.valueType());
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

Expr inner_foldex(Expr ex, bool collapse) {
  if (!ex) return null;
  // auto itr = fastcast!(Itr) (ex.collapse());
  auto itr = fastcast!(Itr) (ex);
  itr = fold(itr, collapse);
  ex = fastcast!(Expr) (itr);
  return ex;
}

Stuple!(int, int)[void*] balance;
Expr outer_foldex(Expr ex, bool collapse) {
  auto backup = ex;
  auto res = inner_foldex(ex, collapse);
  void* caller;
  asm { mov EAX, int ptr [EBP+4]; mov caller, EAX; }
  Stuple!(int, int)* ptr;
  if (auto p = caller in balance) ptr = p;
  else { balance[caller] = Init!(Stuple!(int, int)); ptr = caller in balance; }

  bool oftenUseless;
  auto total = ptr._0 + ptr._1;
  if (total > 128) {
    auto uselessf = ptr._0 * 1f / total;
    if (uselessf > 0.9) oftenUseless = true;
  }
  if (res is backup) {
    ptr._0 ++;
  } else {
    ptr._1 ++;
    if (oftenUseless) {
      logln("opt_itr was usually useless, but not this time (", ptr._0, " / ", ptr._1, "): ", backup, " => ", res);
      asm { int 3; }
    }
  }
  if (oftenUseless && !ptr._1) {
    logln("opt_itr did not do anything");
    asm { int 3; }
  }
  return res;
}

pragma(set_attribute, C_foldex, externally_visible);
extern(C) Expr C_foldex(Expr ex, bool collapse) {
  // return outer_foldex(ex);
  return inner_foldex(ex, collapse);
}

Expr foldex(Expr ex) { return C_foldex(ex, true); }

Statement optst(Statement st) {
  if (!st) return null;
  opt(st);
  return st;
}

Expr optex(Expr ex) {
  if (!ex) return null;
  opt(ex);
  return ex;
}

// Itr[void*] optimized;
void opt_itr(ref Itr it) {
  auto p = cast(void*) it;
  // scope(success) optimized[p] = it;
  
  void fun(ref Itr it) {
    auto p = cast(void*) it;
    // if (auto ip = p in optimized) { it = *ip; return; }
    
    while (true) {
      it.iterate(&fun);
      auto new_it = fold(it, true);
      if (new_it is it) break;
      it = new_it;
    }
  }
  fun(it);
}

void opt(T)(ref T t) {
  Itr it = fastcast!(Itr) (t);
  if (!it) fail(Format(T.stringof, " is not Iterable"));
  opt_itr(it);
  t = fastcast!(T) (it);
  if (!t) fail(Format(T.stringof, " back-cast failed from ", it));
}
