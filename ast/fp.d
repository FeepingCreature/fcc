module ast.fp;

import parseBase, ast.base, ast.types, ast.literals;

Object gotTypeProperty(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty)) return null;
  if (!t2.accept(".")) return null;
  if (resolveType(ty) == Single!(Float)) {
    if (t2.accept("infinity"[])) { text = t2; return fastalloc!(FloatExpr)(float.infinity); }
    if (t2.accept("max"[])) { text = t2; return fastalloc!(FloatExpr)(float.max); }
    if (t2.accept("min"[])) { text = t2; return fastalloc!(FloatExpr)(float.min); }
    if (t2.accept("nan"[])) { text = t2; return fastalloc!(FloatExpr)(float.nan); }
    if (t2.accept("epsilon"[])) { text = t2; return fastalloc!(FloatExpr)(float.epsilon); }
  }
  if (resolveType(ty) == Single!(SysInt)) {
    if (t2.accept("max"[])) { text = t2; return fastalloc!(IntExpr)(int.max); }
    if (t2.accept("min"[])) { text = t2; return fastalloc!(IntExpr)(int.min); }
  }
  if (resolveType(ty) == Single!(Short)) {
    if (t2.accept("max"[])) { text = t2; return fastalloc!(IntExpr)(short.max); }
    if (t2.accept("min"[])) { text = t2; return fastalloc!(IntExpr)(short.min); }
  }
  if (resolveType(ty) == Single!(UByte)) {
    if (t2.accept("max"[])) { text = t2; return fastalloc!(IntExpr)(ubyte.max); }
    if (t2.accept("min"[])) { text = t2; return fastalloc!(IntExpr)(ubyte.min); }
  }
  return null;
}
mixin DefaultParser!(gotTypeProperty, "tree.expr.tprop", "23030");
