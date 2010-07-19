module ast.structfuns;

import ast.fun, ast.nestfun, ast.base, ast.structure, ast.variable,
  ast.pointer, ast.dg, ast.namespace, tools.base: This, This_fn, rmSpace;

import ast.modules;
Object gotStructFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto rs = cast(RelNamespace) namespace();
  if (!rs)
    throw new Exception(Format("Fail: namespace is ", namespace(), ". "));
  auto fun = new RelFunction(rs);
  
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
  Expr baseptr; // unique per instance
  IType basetype; // for mangling purposes
  RelNamespace context;
  private this() { }
  this(RelNamespace rn) {
    context = rn;
    basetype = cast(IType) rn;
    assert(!!basetype);
  }
  RelFunction alloc() { return new RelFunction; }
  RelFunction dup() {
    auto res = cast(RelFunction) super.dup();
    res.context = context;
    res.baseptr = baseptr;
    res.basetype = basetype;
    return res;
  }
  override Object transform(Expr base) {
    assert(!baseptr, Format("RelFun was pretransformed: ", baseptr));
    logln("transform ", this, " with ", base);
    assert(!!cast(RelNamespace) basetype);
    auto res = dup();
    res.baseptr = base;
    return res;
  }
  FunctionPointer typeAsFp() {
    auto res = new FunctionPointer;
    res.ret = type.ret;
    foreach (param; type.params)
      res.args ~= param._0;
    res.args ~= basetype;
    return res;
  }
  mixin defaultIterate!(baseptr);
  override {
    string mangleSelf() {
      return basetype.mangle() ~ "_" ~ super.mangleSelf();
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
