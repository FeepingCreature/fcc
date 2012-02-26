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
  
  return fastcast!(Object) (ex.valueType());
}
mixin DefaultParser!(gotTypeof, "type.of", "45", "type-of");

Object gotSizeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    t2.failparse("Could not get sizeof type");
  text = t2;
  return mkInt(ty.size);
}
mixin DefaultParser!(gotSizeof, "tree.expr.sizeof", "231", "size-of");

import ast.fold;
Object gotTypeStringof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Object obj;
  if (!rest(t2, "type", &obj) && !rest(t2, "tree.expr _tree.expr.arith", &obj))
    return null;
  text = t2;
  if (fastcast!(Iterable) (obj))
    opt(obj);
  return fastcast!(Object)~ mkString(Format(obj));
}
mixin DefaultParser!(gotTypeStringof, "tree.expr.stringof", "232", "string-of");

Object gotTypeMangle(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    t2.failparse("Could not get type for mangle-of");
  text = t2;
  return fastcast!(Object)~ mkString(ty.mangle());
}
mixin DefaultParser!(gotTypeMangle, "tree.expr.type_mangleof", "233", "mangle-of");

Object gotClassId(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  auto cr = fastcast!(ClassRef)~ ty, ir = fastcast!(IntfRef)~ ty;
  Class cl; Intf it;
  if (cr) cl = cr.myClass;
  if (ir) it = ir.myIntf;
  if (!cl && !it) return null;
  text = t2;
  return fastcast!(Object)~ mkString(cl?cl.mangle_id:it.mangle_id);
}
mixin DefaultParser!(gotClassId, "tree.expr.classid", "234", "class-id");

import ast.fun, ast.dg, ast.casting;
Object gotRetType(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  if (!rest(text, "type", &ty))
    return null;
  Expr temp = new Placeholder(ty);
  IType[] tried;
  if (!gotImplicitCast(temp, (IType it) { tried ~= it; return !!fastcast!(FunctionPointer) (it) || !!fastcast!(Delegate) (it); }))
    text.failparse(ty, " is not function-like; tried ", tried);
  auto fun = fastcast!(FunctionPointer)~ temp.valueType(), dg = fastcast!(Delegate)~ temp.valueType();
  if (fun) return fastcast!(Object)~ fun.ret;
  else     return fastcast!(Object)~ dg .ret;
}
mixin DefaultParser!(gotRetType, "type.fun_ret_type", "51", "ReturnType");

import ast.tuples, tools.base;
Object gotParamTypes(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  if (!rest(text, "type", &ty))
    return null;
  Expr temp = new Placeholder(ty);
  IType[] tried;
  if (!gotImplicitCast(temp, (IType it) { tried ~= it; return !!fastcast!(FunctionPointer) (it) || !! fastcast!(Delegate) (it); }))
    text.failparse(ty, " is not function-like; tried ", tried);
  auto fun = fastcast!(FunctionPointer)~ temp.valueType(), dg = fastcast!(Delegate)~ temp.valueType();
  IType flatten(IType it) {
    IType[] res;
    void handle(IType it) {
      if (auto tup = fastcast!(ast.tuples.Tuple) (resolveType(it))) {
        foreach (type; tup.types()) handle(type);
      } else res ~= it;
    }
    handle(it);
    logln(res);
    return mkTuple(res);
  }
  if (fun) return fastcast!(Object) (forcedConvert(flatten(mkTuple(fun.args /map/ ex!("x -> x.type")))));
  else     return fastcast!(Object) (forcedConvert(flatten(mkTuple(dg .args /map/ ex!("x -> x.type")))));
}
mixin DefaultParser!(gotParamTypes, "type.fun_param_type", "52", "ParamTypes");

import ast.conditionals;
Object gotTypesEqual(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  auto t2 = text;
  if (!t2.accept("("))
    t2.failparse("Opening parenthesis expected");
  setupStaticBoolLits;
  Object res;
  while (true) {
    if (t2.accept(")")) break;
    IType ty2;
    if (ty && !t2.accept(","))
      t2.failparse("Comma expected");
    if (!rest(t2, "type", &ty2))
      t2.failparse("Expect type parameter for types-equal! ");
    if (!ty) ty = resolveType(ty2);
    else if (ty != resolveType(ty2))
      res = new ExprWrap(False);
  }
  if (!res) res = fastcast!(Object) (new ExprWrap(True));
  text = t2;
  return res;
}
mixin DefaultParser!(gotTypesEqual, "cond.types-equal", "81", "types-equal");

import ast.conditionals;
Object gotTypeIsTuple(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  auto t2 = text;
  if (!rest(t2, "type", &ty))
    t2.failparse("Expect type parameter for type-is-tuple! ");
  text = t2;
  auto tup = fastcast!(ast.tuples.Tuple) (resolveType(ty));
  setupStaticBoolLits;
  Expr res;
  if (tup) res = True;
  else res = False;
  return fastcast!(Object) (new ExprWrap(res));
}
mixin DefaultParser!(gotTypeIsTuple, "cond.type-is-tuple", "82", "type-is-tuple");
