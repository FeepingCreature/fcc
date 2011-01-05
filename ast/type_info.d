module ast.type_info;

import ast.types, ast.base, ast.parse, ast.int_literal, ast.literals, ast.oop;

// Most of those must come before tree.expr.named
// due to dash-parsing rules!

Object gotTypeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  string match = "tree.expr _tree.expr.arith";
  
  if (!rest(t2, match, &ex))
    t2.failparse("Failed to parse typeof expression");
  text = t2;
  
  return cast(Object) ex.valueType();
}
mixin DefaultParser!(gotTypeof, "type.of", "45", "type-of");

Object gotSizeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    t2.failparse("Could not get sizeof type");
  text = t2;
  return new IntExpr(ty.size);
}
mixin DefaultParser!(gotSizeof, "tree.expr.sizeof", "231", "size-of");

Object gotTypeStringof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Object obj;
  if (!rest(t2, "type", &obj) && !rest(t2, "tree.expr", &obj))
    return null;
  text = t2;
  return cast(Object) mkString(Format(obj));
}
mixin DefaultParser!(gotTypeStringof, "tree.expr.stringof", "232", "string-of");

Object gotTypeMangle(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    t2.failparse("Could not get type for mangle-of");
  text = t2;
  return cast(Object) mkString(ty.mangle());
}
mixin DefaultParser!(gotTypeMangle, "tree.expr.type_mangleof", "233", "mangle-of");

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
  text = t2;
  return cast(Object) mkString(cl?cl.mangle_id:it.mangle_id);
}
mixin DefaultParser!(gotClassId, "tree.expr.classid", "234", "class-id");

import ast.fun, ast.dg, ast.casting;
Object gotRetType(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  if (!rest(text, "type", &ty))
    return null;
  Expr temp = new Placeholder(ty);
  IType[] tried;
  if (!gotImplicitCast(temp, (IType it) { tried ~= it; return !!cast(FunctionPointer) it || !!cast(Delegate) it; }))
    text.failparse(ty, " is not function-like; tried ", tried);
  auto fun = cast(FunctionPointer) temp.valueType(), dg = cast(Delegate) temp.valueType();
  if (fun) return cast(Object) fun.ret;
  else     return cast(Object) dg .ret;
}
mixin DefaultParser!(gotRetType, "type.fun_ret_type", "51", "ReturnType");

import ast.tuples;
Object gotParamTypes(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  if (!rest(text, "type", &ty))
    return null;
  Expr temp = new Placeholder(ty);
  IType[] tried;
  if (!gotImplicitCast(temp, (IType it) { tried ~= it; return !!cast(FunctionPointer) it || !! cast(Delegate) it; }))
    text.failparse(ty, " is not function-like; tried ", tried);
  auto fun = cast(FunctionPointer) temp.valueType(), dg = cast(Delegate) temp.valueType();
  if (fun) return mkTuple(fun.args);
  else     return mkTuple(dg .args);
}
mixin DefaultParser!(gotParamTypes, "type.fun_param_type", "52", "ParamTypes");
