module ast.structfuns;

import ast.fun, ast.nestfun, ast.base, ast.structure, ast.variable, ast.pointer,
  tools.base: This, This_fn, rmSpace;

class StructMemberCall : FunCall {
  Expr strct;
  mixin This!("strct");
  override void emitAsm(AsmFile af) {
    callNested(af, fun.type.ret, params, fun.mangleSelf, strct);
  }
  override Type valueType() {
    return fun.type.ret;
  }
}

class StructMemberFunction : Function {
  Expr strct;
  this(Expr ex) {
    strct = ex;
    assert(!!cast(Structure) strct.valueType());
  }
  mixin defaultIterate!(strct);
  override {
    string mangleSelf() {
      return (strct.valueType()).mangle() ~ "_" ~ super.mangleSelf();
    }
    string mangle(string name, Type type) {
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
      if (strt.lookupMember(name) == -1) return null;
      
      return cast(Object) mkMemberAccess(strct, name);
    }
  }
}
