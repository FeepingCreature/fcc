module ast.type_of;

import ast.types, ast.base, ast.parse, ast.int_literal;

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

Object gotSizeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("sizeof(")) {
    auto t3 = t2;
    Type ty; Expr ex;
    if (rest(t3, "type", &ty) && t3.accept(")")) {
      text = t3;
      return new IntExpr(ty.size);
    }
    if (rest(t3, "tree.expr", &ex) && t3.accept(")")) {
      text = t3;
      return new IntExpr(ex.valueType().size);
    }
    throw new Exception(Format(
      "Failed to match parameter for sizeof expression at ", t2.next_text()
    ));
  } else return null;
}
mixin DefaultParser!(gotSizeof, "tree.expr.sizeof", "51");
