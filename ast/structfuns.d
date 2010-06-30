module ast.structfuns;

import ast.fun, ast.nestfun, ast.base, ast.structure, ast.variable, ast.pointer,
  ast.namespace, tools.base: This, This_fn, rmSpace;

class StructMemberCall : FunCall {
  Expr strct;
  mixin This!("strct");
  override void emitAsm(AsmFile af) {
    // TODO: make temporary
    auto lv = cast(LValue) strct;
    assert(lv);
    callNested(af, fun.type.ret, params, fun.mangleSelf, new RefExpr(lv));
  }
  override IType valueType() {
    return fun.type.ret;
  }
}

class StructMemberFunction : Function, RelTransformable {
  Expr strct;
  Structure context;
  this(Structure st) { context = st; }
  Object transform(Expr base) {
    assert(!strct || strct is base);
    strct = base;
    assert(!!cast(Structure) strct.valueType());
    return this;
  }
  mixin defaultIterate!(strct);
  override {
    string mangleSelf() {
      return (strct.valueType()).mangle() ~ "_" ~ super.mangleSelf();
    }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ type.mangle()~"_"~name;
    }
    FunCall mkCall() {
      return new StructMemberCall(strct);
    }
    int fixup() {
      auto cur = super.fixup();
      add(new Variable(new Pointer(context), "__base_ptr", cur));
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

import ast.modules;
Object gotStructFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto sns = cast(Structure) namespace();
  if (!sns)
    throw new Exception(Format("Fail: namespace is ", namespace(), ". "));
  auto fun = new StructMemberFunction(sns);
  
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
      auto smf = cast(StructMemberFunction) mvar;
      if (!smf) return null;
      text = t2;
      smf.strct = ex;
      return smf;
    } else return null;
  };
}
mixin DefaultParser!(gotStructFun, "tree.rhs_partial.structfun");
