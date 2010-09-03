module ast.slice;

import ast.base, ast.arrays, ast.pointer, ast.math, ast.modules, ast.fun,
  ast.structure, ast.parse, ast.int_literal, ast.static_arrays;

Expr mkPointerSlice(Expr ptr, Expr from, Expr to) {
  return new ArrayMaker(
    new AddExpr(ptr, from),
    new SubExpr(to, from)
  );
}

Expr mkArraySlice(Expr array, Expr from = null, Expr to = null) {
  return new ArrayMaker(
    new AddExpr(new MemberAccess_Expr(arrayToStruct(array), "ptr"), from),
    new SubExpr(to, from)
  );
}

import ast.iterator, ast.casting;
Object gotSliceExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!cast(Array) ex.valueType() && !cast(Pointer) ex.valueType()) return null;
    auto t2 = text;
    Expr range;
    if (t2.accept("[") && t2.accept("]") || (t2 = text, true) &&
        t2.accept("[") && rest(t2, "tree.expr", &range, (Expr ex) { return !!cast(Range) ex.valueType(); }) && t2.accept("]")
    ) {
      Expr from, to;
      if (range) {
        auto casted = new RCE((cast(Range) range.valueType()).wrapper, range);
        from = iparse!(Expr, "slice_range_from", "tree.expr")("ex.cur", "ex", casted);
        to   = iparse!(Expr, "slice_range_to",   "tree.expr")("ex.end", "ex", casted);
      }
      if (!from) from = new IntExpr(0);
      if (!to) {
        if (!cast(Array) ex.valueType()) return null;
        // assert(!!cast(Array) ex.valueType(), "Cannot take \"full slice\" over pointer! ");
        to = getArrayLength(ex);
      }
      if (from.valueType().size() != 4) throw new Exception(Format("Invalid slice start: ", from));
      if (to.valueType().size() != 4) throw new Exception(Format("Invalid slice end: ", from));
      text = t2;
      if (cast(Array) ex.valueType()) return cast(Object) mkArraySlice(ex, from, to);
      else {
        return cast(Object) mkPointerSlice(ex, from, to);
      }
    } else return null;
  };
}
mixin DefaultParser!(gotSliceExpr, "tree.rhs_partial.slice");

Statement getSliceAssign(Expr slice, Expr array) {
  IType elemtype;
  if (auto sa = cast(StaticArray) array.valueType())
    elemtype = sa.elemType;
  else if (auto ar = cast(Array) array.valueType())
    elemtype = ar.elemType;
  else
    throw new Exception(Format("Can't assign to slice: ", array));
  
  auto fc = (cast(Function) sysmod.lookup("memcpy")).mkCall;
  fc.params ~= getArrayPtr(slice);
  fc.params ~= getArrayPtr(array);
  fc.params ~= new MulExpr(getArrayLength(array), new IntExpr(elemtype.size));
  return new ExprStatement(fc);
}

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
        error = Format("Mismatching types in slice assignment: ", dest, " <- ", src.valueType());
        return null;
      }
      text = t2;
      // TODO: assert on size
      return cast(Object) getSliceAssign(dest, src);
    } else throw new Exception("Failed to parse slice-assignment value at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotSliceAssignment, "tree.semicol_stmt.assign_slice", "10");
