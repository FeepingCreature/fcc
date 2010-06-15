module ast.slice;

import ast.base, ast.arrays, ast.pointer, ast.math, ast.structure, ast.parse;

Expr mkArraySlice(Expr array, Expr from, Expr to) {
  return new ArrayMaker(
    new AddExpr(new MemberAccess_Expr(arrayToStruct(array), "ptr"), from),
    new SubExpr(to, from)
  );
}

Expr mkPointerSlice(Expr ptr, Expr from, Expr to) {
  return new ArrayMaker(
    new AddExpr(ptr, from),
    new SubExpr(to, from)
  );
}

Object gotArraySliceExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!cast(Array) ex.valueType() && !cast(Pointer) ex.valueType()) return null;
    auto t2 = text;
    Expr from, to;
    if (t2.accept("[") && rest(t2, "tree.expr", &from) && t2.accept("..") && rest(t2, "tree.expr", &to) && t2.accept("]")) {
      if (from.valueType().size() != 4) throw new Exception(Format("Invalid slice start: ", from));
      if (to.valueType().size() != 4) throw new Exception(Format("Invalid slice end: ", from));
      text = t2;
      if (cast(Array) ex.valueType()) return cast(Object) mkArraySlice(ex, from, to);
      else return cast(Object) mkPointerSlice(ex, from, to);
    } else return null;
  };
}
mixin DefaultParser!(gotArraySliceExpr, "tree.rhs_partial.slice");
