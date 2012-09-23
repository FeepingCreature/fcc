module ast.type_info;

import ast.types, ast.base, ast.parse, ast.int_literal, ast.literals, ast.oop, ast.vector, ast.structure, ast.pointer;

// Most of those must come before tree.expr.named
// due to dash-parsing rules!

Object gotTypeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  string match = "tree.expr _tree.expr.arith";
  
  if (!rest(t2, match, &ex))
    t2.failparse("Failed to parse typeof expression"[]);
  text = t2;
  
  return fastcast!(Object) (ex.valueType());
}
mixin DefaultParser!(gotTypeof, "type.of"[], "45"[], "type-of"[]);

Object gotSizeof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type"[], &ty))
    t2.failparse("Could not get sizeof type"[]);
  text = t2;
  return mkInt(ty.size);
}
mixin DefaultParser!(gotSizeof, "tree.expr.sizeof"[], "231"[], "size-of"[]);

import ast.fold;
Object gotTypeStringof(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool detailed;
  if (t2.accept("detailed"[])) detailed = true;
  Object obj;
  if (!rest(t2, "type"[], &obj) && !rest(t2, "tree.expr _tree.expr.arith"[], &obj))
    return null;
  if (fastcast!(Iterable) (obj)) opt(obj);
  text = t2;
  auto res = qformat(obj);
  if (auto it = fastcast!(Iterable) (obj)) {
    void add(ref Iterable it) {
      res ~= (fastcast!(Object) (it)).classinfo.name;
      res ~= "(";
      it.iterate(&add);
      res ~= ")";
    }
    if (detailed) add(it);
  }
  return fastcast!(Object) (mkString(res));
}
mixin DefaultParser!(gotTypeStringof, "tree.expr.stringof"[], "232"[], "string-of"[]);

Object gotTypeMangle(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type"[], &ty))
    t2.failparse("Could not get type for mangle-of"[]);
  text = t2;
  return fastcast!(Object)~ mkString(ty.mangle());
}
mixin DefaultParser!(gotTypeMangle, "tree.expr.type_mangleof"[], "233"[], "mangle-of"[]);

Object gotClassId(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type"[], &ty))
    return null;
  auto cr = fastcast!(ClassRef)~ ty, ir = fastcast!(IntfRef)~ ty;
  Class cl; Intf it;
  if (cr) cl = cr.myClass;
  if (ir) it = ir.myIntf;
  if (!cl && !it) return null;
  text = t2;
  return fastcast!(Object)~ mkString(cl?cl.mangle_id:it.mangle_id);
}
mixin DefaultParser!(gotClassId, "tree.expr.classid"[], "234"[], "class-id"[]);

import ast.fun, ast.dg, ast.casting;
Object gotRetType(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  if (!rest(text, "type"[], &ty))
    return null;
  Expr temp = fastalloc!(Placeholder)(ty);
  IType[] tried;
  if (!gotImplicitCast(temp, (IType it) { tried ~= it; return !!fastcast!(FunctionPointer) (it) || !!fastcast!(Delegate) (it); }))
    text.failparse(ty, " is not function-like; tried "[], tried);
  auto fun = fastcast!(FunctionPointer)~ temp.valueType(), dg = fastcast!(Delegate)~ temp.valueType();
  if (fun) return fastcast!(Object)~ fun.ret;
  else     return fastcast!(Object)~ dg .ret;
}
mixin DefaultParser!(gotRetType, "type.fun_ret_type"[], "51"[], "ReturnType"[]);

import ast.tuples, tools.base;
Object gotParamTypes(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  if (!rest(text, "type"[], &ty))
    return null;
  Expr temp = fastalloc!(Placeholder)(ty);
  IType[] tried;
  if (!gotImplicitCast(temp, (IType it) { tried ~= it; return !!fastcast!(FunctionPointer) (it) || !! fastcast!(Delegate) (it); }))
    text.failparse(ty, " is not function-like; tried "[], tried);
  auto fun = fastcast!(FunctionPointer)~ temp.valueType(), dg = fastcast!(Delegate)~ temp.valueType();
  IType flatten(IType it) {
    IType[] res;
    void handle(IType it) {
      if (auto tup = fastcast!(ast.tuples.Tuple) (resolveType(it))) {
        foreach (type; tup.types()) handle(type);
      } else res ~= it;
    }
    handle(it);
    return mkTuple(res);
  }
  Argument[] args;
  if (fun) args = fun.args;
  else     args =  dg.args;
  foreach (arg; args) if (!arg.type) text.failparse("Function arguments incomplete: ", arg.name, " untyped");
  return fastcast!(Object) (forcedConvert(flatten(mkTuple(args /map/ ex!("x -> x.type"[])))));
}
mixin DefaultParser!(gotParamTypes, "type.fun_param_type"[], "52"[], "ParamTypes"[]);

import ast.conditionals;
Object gotTypesEqual(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  auto t2 = text;
  if (!t2.accept("("[]))
    t2.failparse("Opening parenthesis expected"[]);
  setupStaticBoolLits;
  Object res;
  while (true) {
    if (t2.accept(")"[])) break;
    IType ty2;
    if (ty && !t2.accept(","[]))
      t2.failparse("Comma expected"[]);
    if (!rest(t2, "type"[], &ty2))
      t2.failparse("Expect type parameter for types-equal! "[]);
    if (!ty) ty = resolveType(ty2);
    else if (ty != resolveType(ty2))
      res = fastcast!(Object)(False);
  }
  if (!res) res = fastcast!(Object)(True);
  text = t2;
  return res;
}
mixin DefaultParser!(gotTypesEqual, "tree.expr.types-equal", "2351", "types-equal");

import ast.conditionals;
Object gotTypeIsTuple(ref string text, ParseCb cont, ParseCb rest) {
  logSmart!(false)("WARN: 'type-is-tuple' is deprecated; please use 'type-is tuple' instead");
  logSmart!(false)(" at ", text.nextText());
  IType ty;
  auto t2 = text;
  if (!rest(t2, "type"[], &ty))
    t2.failparse("Expect type parameter for type-is-tuple! "[]);
  text = t2;
  auto tup = fastcast!(ast.tuples.Tuple) (resolveType(forcedConvert(ty)));
  setupStaticBoolLits;
  Expr res;
  if (tup) res = True;
  else res = False;
  return fastcast!(Object)(res);
}
mixin DefaultParser!(gotTypeIsTuple, "tree.expr.type-is-tuple", "2352", "type-is-tuple");

import ast.conditionals, ast.arrays;
Object gotTypeIs(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string mode;
  if (t2.accept("tuple")) mode = "tuple";
  if (t2.accept("array")) mode = "array";
  if (t2.accept("class")) mode = "class";
  if (t2.accept("interface")) mode = "interface";
  if (t2.accept("function")) mode = "function";
  if (t2.accept("delegate")) mode = "delegate";
  if (t2.accept("vector")) mode = "vector";
  if (t2.accept("struct")) mode = "struct";
  if (t2.accept("pointer")) mode = "pointer";
  if (!mode) t2.failparse("type-is expected type qualifier");
  IType ty;
  if (!rest(t2, "type"[], &ty))
    t2.failparse("Expect type parameter for type-is! "[]);
  ty = resolveType(forcedConvert(ty));
  text = t2;
  
  bool res;
  switch (mode) {
    case "tuple": res = !!fastcast!(ast.tuples.Tuple) (ty); break;
    case "array": res = !!fastcast!(Array) (ty) || !!fastcast!(ExtArray) (ty); break;
    case "class": res = !!fastcast!(ClassRef) (ty); break;
    case "interface": res = !!fastcast!(IntfRef) (ty); break;
    case "function": res = !!fastcast!(FunctionPointer) (ty); break;
    case "delegate": res = !!fastcast!(Delegate) (ty); break;
    case "vector": res = !!fastcast!(Vector) (ty); break;
    case "struct": res = !!fastcast!(Structure) (ty); break;
    case "pointer": res = !!fastcast!(Pointer) (ty); break;
  }
  setupStaticBoolLits;
  Expr ex;
  if (res) ex = True;
  else ex = False;
  return fastcast!(Object)(ex);
}
mixin DefaultParser!(gotTypeIs, "tree.expr.type-is", "2353", "type-is");

import ast.namespace;
Object gotExists(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool local;
  if (t2.accept("local")) local = true;
  string ident;
  if (!t2.gotIdentifier(ident))
    t2.failparse("is-defined expects identifier");
  text = t2;
  
  setupStaticBoolLits;
  if (namespace().lookup(ident, local))
    return fastcast!(Object) (True);
  else
    return fastcast!(Object) (False);
}
mixin DefaultParser!(gotExists, "tree.expr.is-defined", "2354", "is-defined");

Object gotConvertsTo(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType it;
  if (!rest(t2, "type"[], &it))
    t2.failparse("implicitly-converts-to expects target type");
  it = resolveType(it);
  
  Expr ex;
  if (!rest(t2, "tree.expr"[], &ex))
    t2.failparse("implicitly-converts-to expects source expr");
  
  it = resolveType(it);
  ex = forcedConvert(ex);
  
  text = t2;
  if (gotImplicitCast(ex, it, (IType it2) { return test(resolveType(it2) == it); }))
    return fastcast!(Object)(True);
  else
    return fastcast!(Object)(False);
}
mixin DefaultParser!(gotConvertsTo, "tree.expr.implicitly-converts-to", "2355", "implicitly-converts-to");
