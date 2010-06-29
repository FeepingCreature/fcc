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
/*
import ast.parse;
Object gotStructFun(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  return lhs_partial.using = delegate Object(Expr ex) {
    auto strtype = cast(Structure) ex.valueType();
    if (!strtype) return null;
    string member;
    if (t2.accept(".") && t2.gotIdentifier(member)) {
      auto entry = 
    }
  };
  
  auto ex = cast(Expr) lhs_partial();
  if (!ex) return null;
  if (!cast(Structure) ex.valueType())
    return null;
  
  string member;
  
  auto pre_ex = ex;
  if (t2.accept(".") && t2.gotIdentifier(member)) {
    auto st = cast(Structure) ex.valueType();
    if (st.lookupMember(member) == -1) {
      error = Format(member, " is not a member of ", st.name, "!");
      return null;
    }
    ex = mkMemberAccess(ex, member);
    text = t2;
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_member");
*/