module ast.type_of;

import ast.types, ast.base, ast.parse;

Object gotTypeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!(
    t2.accept("typeof(") &&
    rest(t2, "tree.expr", &ex) &&
    t2.accept(")")
  ))
    return null;
  text = t2;
  return cast(Object) ex.valueType();
}
mixin DefaultParser!(gotTypeof, "type.of", "45");
