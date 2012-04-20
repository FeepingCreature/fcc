module ast.trivial;

import ast.base, ast.literal_string, ast.casting, ast.structure, ast.arrays, ast.math;

// An expression is trivial if it can be evaluated without significant cost or side effects.

bool isTrivial(Expr ex) {
  auto lv = fastcast!(LValue) (ex);
  if (lv) return true;
  if (fastcast!(Literal) (ex) || fastcast!(StringExpr) (ex)) return true;
  if (auto rc = fastcast!(RCE) (ex)) return isTrivial(rc.from);
  if (auto mae = fastcast!(MemberAccess_Expr) (ex)) return isTrivial(mae.base);
  if (auto am = fastcast!(ArrayMaker) (ex)) {
    return isTrivial(am.ptr) && isTrivial(am.length) && (!am.cap || isTrivial(am.cap));
  }
  if (auto al = fastcast!(ArrayLength_Base) (ex)) {
    return isTrivial(al.array);
  }
  if (auto sl = fastcast!(StructLiteral) (ex)) {
    foreach (subex; sl.exprs)
      if (!isTrivial(subex)) return false;
    return true;
  }
  if (auto aibe = fastcast!(AsmIntBinopExpr) (ex)) {
    return isTrivial(aibe.e1) && isTrivial(aibe.e2);
  }
  // logln("Not trivial: "[], (cast(Object) ex).classinfo.name, " : "[], ex);
  return false;
}

static this() {
  ast.base.isTrivial = &isTrivial;
}
