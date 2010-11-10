module ast.nullcasts;

import ast.base, ast.casting, ast.int_literal, ast.aliasing, ast.tuples;
import ast.arrays, ast.dg, ast.fun;
bool isNull(Expr ex) {
  auto ea = cast(ExprAlias) ex;
  if (ea) ex = ea.base;
  auto rce = cast(RCE) ex;
  if (!rce) return false;
  ex = rce.from;
  auto ie = cast(IntExpr) ex;
  if (!ie) return false;
  return ie.num == 0;
}

static this() {
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && cast(FunctionPointer) expect) {
      return reinterpret_cast(expect, ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && cast(Delegate) expect) {
      return reinterpret_cast(expect, mkTupleExpr(ex, ex));
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && cast(Array) expect) {
      return reinterpret_cast(expect, mkTupleExpr(ex, ex));
    }
    return null;
  };
}
