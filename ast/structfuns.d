module ast.structfuns;

import ast.fun, ast.nestfun, ast.base, ast.structure, ast.variable,
  ast.pointer, ast.dg, ast.namespace, tools.base: This, This_fn, rmSpace;

import ast.modules;
Object gotStructFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto sns = cast(Structure) namespace();
  if (!sns)
    throw new Exception(Format("Fail: namespace is ", namespace(), ". "));
  auto fun = new RelFunction(sns);
  
  if (auto res = gotGenericFunDef(fun, cast(Namespace) null, false, text, cont, rest)) {
    namespace().get!(Module).entries ~= cast(Tree) res;
    return res;
  } else return null;
}
mixin DefaultParser!(gotStructFunDef, "struct_member.struct_fundef");

import ast.parse, tools.log;
Object gotStructFun(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  return lhs_partial.using = delegate Object(Expr ex) {
    logln("match a struct fun @", t2.next_text());
    auto strtype = cast(Structure) ex.valueType();
    if (!strtype) return null;
    string member;
    if (t2.accept(".") && t2.gotIdentifier(member)) {
      auto mvar = strtype.lookup(member);
      if (!mvar) return null;
      logln("Got a struct fun? ", mvar);
      auto smf = cast(RelFunction) mvar;
      if (!smf) return null;
      text = t2;
      return smf.transform(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotStructFun, "tree.rhs_partial.structfun");

class RelFunCall : FunCall {
  Expr baseptr;
  mixin This!("baseptr");
  override void emitAsm(AsmFile af) {
    // TODO: make temporary
    auto lv = cast(LValue) baseptr;
    assert(lv);
    callDg(af, fun.type.ret, params,
      new DgConstructExpr(fun.getPointer(), new RefExpr(lv)));
  }
  override IType valueType() {
    return fun.type.ret;
  }
}

class RelFunction : Function, RelTransformable {
  Expr baseptr;
  RelNamespace context;
  this(RelNamespace rn) { context = rn; }
  Object transform(Expr base) {
    assert(!baseptr);
    baseptr = base;
    assert(!!cast(RelNamespace) baseptr.valueType());
    return this;
  }
  FunctionPointer typeAsFp() {
    auto res = new FunctionPointer;
    res.ret = type.ret;
    foreach (param; type.params)
      res.args ~= param._0;
    res.args ~= baseptr.valueType();
    return res;
  }
  mixin defaultIterate!(baseptr);
  override {
    string mangleSelf() {
      return (baseptr.valueType()).mangle() ~ "_" ~ super.mangleSelf();
    }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ type.mangle()~"_"~name;
    }
    FunCall mkCall() {
      return new RelFunCall(baseptr);
    }
    int fixup() {
      auto cur = super.fixup();
      add(new Variable(new Pointer(cast(IType) context), "__base_ptr", cur));
      return cur + 4;
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, true);
      if (res) return res;
      else if (local) return null;
      
      if (auto res = context.lookupRel(
        name,
        new DerefExpr(cast(Expr) lookup("__base_ptr", true))
      ))
        return res;
      
      return null;
    }
  }
}
