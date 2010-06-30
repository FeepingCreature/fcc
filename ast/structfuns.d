module ast.structfuns;

import ast.fun, ast.nestfun, ast.base, ast.structure, ast.variable, ast.pointer,
  ast.namespace, tools.base: This, This_fn, rmSpace;

class StructMemberCall : FunCall {
  Expr strct;
  mixin This!("strct");
  override void emitAsm(AsmFile af) {
    callNested(af, fun.type.ret, params, fun.mangleSelf, strct);
  }
  override IType valueType() {
    return fun.type.ret;
  }
}

class StructMemberFunction : Function, RelTransformable {
  Expr strct;
  this() { }
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
      add(new Variable(Single!(Pointer, Single!(Void)), "__base_ptr", cur));
      return cur + 4;
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, true);
      if (res) return res;
      else if (local) return null;
      
      auto strt = cast(Structure) strct.valueType();
      if (!strt.lookup(name)) return null;
      
      return cast(Object) mkMemberAccess(strct, name);
    }
  }
}

Object gotStructFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto fun = new StructMemberFunction;
  return gotGenericFunDef(fun, cast(Namespace) null, text, cont, rest);
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
      auto smf = cast(StructMemberFunction) mvar;
      if (!smf) return null;
      smf.strct = ex;
      return smf;
    } else return null;
  };
}
mixin DefaultParser!(gotStructFun, "tree.rhs_partial.structfun");
