module ast.slice;

import ast.base, ast.arrays, ast.pointer, ast.math,
  ast.structure, ast.parse, ast.int_literal;

Expr mkPointerSlice(Expr ptr, Expr from, Expr to) {
  return new ArrayMaker(
    new AddExpr(ptr, from),
    new SubExpr(to, from),
    new IntExpr(0)
  );
}

Expr mkArraySlice(Expr array, Expr from, Expr to) {
  return new ArrayMaker(
    new AddExpr(new MemberAccess_Expr(arrayToStruct(array), "ptr"), from),
    new SubExpr(to, from),
    new IntExpr(0)
  );
}

Object gotSliceExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!cast(Array) ex.valueType() && !cast(Pointer) ex.valueType()) return null;
    auto t2 = text;
    Expr from, to;
    if (t2.accept("[") && t2.accept("]") || (t2 = text, true) &&
        t2.accept("[") && rest(t2, "tree.expr", &from) && t2.accept("..") && rest(t2, "tree.expr", &to) && t2.accept("]")
    ) {
      if (!from) from = new IntExpr(0);
      if (!to) {
        assert(!!cast(Array) ex.valueType(), "Cannot take \"full slice\" over pointer! ");
        to = getArrayLength(ex);
      }
      if (from.valueType().size() != 4) throw new Exception(Format("Invalid slice start: ", from));
      if (to.valueType().size() != 4) throw new Exception(Format("Invalid slice end: ", from));
      text = t2;
      if (cast(Array) ex.valueType()) return cast(Object) mkArraySlice(ex, from, to);
      else return cast(Object) mkPointerSlice(ex, from, to);
    } else return null;
  };
}
mixin DefaultParser!(gotSliceExpr, "tree.rhs_partial.slice");

import ast.namespace, tools.log;
Object gotSliceAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr dest, src;
  if (rest(t2, "tree.expr >tree.expr.arith", &dest) && t2.accept("=")) {
    auto ar = cast(Array) dest.valueType();
    if (!ar) return null;
    if (cast(LValue) dest) return null; // leave to normal assignment
    if (rest(t2, "tree.expr", &src)) {
      if (dest.valueType() != src.valueType()) {
        throw new Exception(Format("Mismatching types in assignment: ", dest, " <- ", src.valueType()));
      }
      text = t2;
      // TODO: assert on size
      logln("src is ", src, "; ", src.valueType());
      return cast(Object) iparse!(Statement, "slice_assign_as_memcpy", "tree.semicol_stmt.expr")
        ("memcpy(dest.ptr, src.ptr, src.length * sizeof(typeof(src[0])))",
          "dest", dest,
          "src", src
        );
    } else throw new Exception("Failed to parse slice-assignment value at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotSliceAssignment, "tree.semicol_stmt.assign_slice", "10");
