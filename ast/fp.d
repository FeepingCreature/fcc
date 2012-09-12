module ast.fp;

import parseBase, ast.base, ast.types, ast.literals;

Object gotFloatProperty(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept(".")) return null;
  if (t2.accept("infinity"[])) { text = t2; return fastalloc!(FloatExpr)(float.infinity); }
  if (t2.accept("nan"[])) { text = t2; return fastalloc!(FloatExpr)(float.nan); }
  if (t2.accept("epsilon"[])) { text = t2; return fastalloc!(FloatExpr)(float.epsilon); }
  return null;
}
mixin DefaultParser!(gotFloatProperty, "tree.expr.fprop", "23030", "float");

Object gotIntProperty(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept(".")) return null;
  if (t2.accept("max"[])) { text = t2; return fastalloc!(IntExpr)(int.max); }
  return null;
}
mixin DefaultParser!(gotIntProperty, "tree.expr.iprop", "23031", "int");
