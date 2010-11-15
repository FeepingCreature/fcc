module ast.type_of;

import ast.types, ast.base, ast.parse, ast.int_literal, ast.literals, ast.oop;

Object gotTypeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!t2.accept("typeof(")) return null;
  if (!(rest(t2, "tree.expr", &ex) && t2.accept(")")))
    t2.failparse("Failed to parse typeof expression");
  text = t2;
  return cast(Object) ex.valueType();
}
mixin DefaultParser!(gotTypeof, "type.of", "45");

Object gotSizeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  if (!t2.accept(".sizeof"))
    return null;
  text = t2;
  return new IntExpr(ty.size);
}
mixin DefaultParser!(gotSizeof, "tree.expr.sizeof", "51");

Object gotTypeStringof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  if (!t2.accept(".stringof")) return null;
  text = t2;
  return cast(Object) mkString(Format(ty));
}
mixin DefaultParser!(gotTypeStringof, "tree.expr.type_stringof", "30");

Object gotTypeMangle(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  if (!t2.accept(".mangleof")) return null;
  text = t2;
  return cast(Object) mkString(ty.mangle());
}
mixin DefaultParser!(gotTypeMangle, "tree.expr.type_mangleof", "301");

Object gotClassId(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  auto cr = cast(ClassRef) ty, ir = cast(IntfRef) ty;
  Class cl; Intf it;
  if (cr) cl = cr.myClass;
  if (ir) it = ir.myIntf;
  if (!cl && !it) return null;
  if (!t2.accept(".classid")) return null;
  text = t2;
  return cast(Object) mkString(cl?cl.mangle_id:it.mangle_id);
}
mixin DefaultParser!(gotClassId, "tree.expr.classid", "302");

import tools.log;
Object gotPartialStringof(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (text.accept(".stringof")) {
      // logln("got ", Format(ex));
      return cast(Object) mkString(Format(ex));
    }
    else return null;
  };
}
mixin DefaultParser!(gotPartialStringof, "tree.rhs_partial.stringof");
