module ast.dg;

import ast.base, ast.parse, ast.vardecl, ast.namespace, ast.structure,
  ast.pointer, ast.fun;

class mkDelegate : Expr {
  abstract IType valueType();
  Expr ptr, data;
  this(Expr ptr, Expr data) {
    if (ptr.valueType().size != 4) {
      asm { int 3; }
      throw new Exception(Format("Cannot construct delegate from ", ptr, " (data ", data, ")!"));
    }
    this.ptr = ptr;
    this.data = data;
  }
  mixin defaultIterate!(ptr, data);
  override string toString() { return Format("dg(ptr=", ptr, ", data=", data, ")"); }
  override void emitAsm(AsmFile af) {
    mixin(mustOffset("nativePtrSize * 2"));
    // TODO: stack growth order
    data.emitAsm(af);
    ptr.emitAsm(af);
  }
}

import tools.log;
// type-deduced!
class DgConstructExpr : mkDelegate {
  this(Expr fun, Expr base) {
    if (auto dg = cast(Delegate) fun.valueType()) {
      assert(false);
      fun = iparse!(Expr, "dg_to_fun", "tree.expr")("fun.fun", "fun", fun);
    }
    super(fun, base);
  }
  override IType valueType() {
    auto ft = cast(FunctionPointer) ptr.valueType();
    // logln("ptr is ", ptr, ", data ", data, ", ft ", ft);
    // logln("ptr type is ", ptr.valueType());
    assert(ft.args.length);
    assert(ft.args[$-1].size == data.valueType().size);
    return new Delegate(ft.ret, ft.args[0 .. $-1]);
  }
}

// close fp over ptr to dg
Object gotFpCloseExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto fptype = cast(FunctionPointer) ex.valueType();
    if (!fptype) return null;
    
    if (t2.accept(".toDg(")) {
      Expr dataptr;
      if (!(rest(t2, "tree.expr", &dataptr) && t2.accept(")")))
        throw new Exception(Format(
          "Invalid syntax for toDg at ", t2.next_text()
        ));
      text = t2;
      return new DgConstructExpr(ex, dataptr);
    } else return null;
  };
}
mixin DefaultParser!(gotFpCloseExpr, "tree.rhs_partial.fpclose", null, true);

class Delegate : Type {
  IType ret;
  IType[] args;
  this() { }
  this(IType ret, IType[] args) { this.ret = ret; this.args = args; }
  override {
    string toString() {
      return Format(ret, " delegate ", args);
    }
    int size() {
      return nativePtrSize * 2;
    }
    string mangle() {
      auto res = "dg_ret_"~ret.mangle()~"_args";
      if (!args.length) res ~= "_none";
      else foreach (arg; args)
        res ~= "_"~arg.mangle();
      return res;
    }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      auto dg = cast(Delegate) ty;
      if (dg.ret != ret) return false;
      foreach (i, arg; dg.args)
        if (arg != args[i]) return false;
      return true;
    }
  }
}

IType dgAsStructType(Delegate dgtype) {
  auto res = new Structure(null);
  new RelMember("fun",
    new FunctionPointer(
      dgtype.ret,
      dgtype.args ~ cast(IType) voidp
    ),
    res
  );
  new RelMember("data", voidp, res);
  return res;
}

import ast.casting;
Expr dgAsStruct(Expr ex) {
  auto dgtype = cast(Delegate) ex.valueType();
  assert(!!dgtype);
  if (auto lv = cast(LValue) ex) {
    return new ReinterpretCast!(LValue) (dgAsStructType(dgtype), lv);
  } else {
    return new ReinterpretCast!(Expr) (dgAsStructType(dgtype), ex);
  }
}

Object gotDgAsStruct(ref string st, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(st, "tree.expr ^selfrule", &ex))
    return null;
  if (!cast(Delegate) ex.valueType())
    return null;
  return cast(Object) dgAsStruct(ex);
}
mixin DefaultParser!(gotDgAsStruct, "tree.expr.dg_struct", "912");

class DgCall : Expr {
  Expr dg;
  Expr[] params;
  mixin defaultIterate!(dg, params);
  override void emitAsm(AsmFile af) {
    auto dgtype = cast(Delegate) dg.valueType();
    callDg(af, dgtype.ret, params, dg);
  }
  override IType valueType() {
    return (cast(Delegate) dg.valueType()).ret;
  }
}

Object gotDgCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto dgtype = cast(Delegate) ex.valueType();
    if (!dgtype) return null;
    
    auto dc = new DgCall;
    dc.dg = ex;
    
    if (t2.accept("(")) {
      dc.params = matchCall(t2, Format("delegate ", ex), dgtype.args, rest);
      text = t2;
      return dc;
    } else return null;
  };
}
mixin DefaultParser!(gotDgCallExpr, "tree.rhs_partial.dgcall", null, true);

// stolen in turn from ast.fun
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb rest) {
    IType ptype;
    Stuple!(IType, string)[] list;
    auto t2 = text;
    if (t2.accept("delegate") &&
      t2.gotParlist(list, rest)
    ) {
      text = t2;
      auto res = new Delegate;
      res.ret = cur;
      foreach (entry; list) res.args ~= entry._0;
      return res;
    } else return null;
  };
}

void callDg(AsmFile dest, IType ret, Expr[] params, Expr dg) {
  dest.comment("Begin delegate call");
  
  auto dgs = dgAsStruct(dg);
  params ~= mkMemberAccess(dgs, "data");
  
  foreach_reverse (param; params) {
    dest.comment("Push ", param);
    param.emitAsm(dest);
  }
  
  mkMemberAccess(dgs, "fun").emitAsm(dest);
  dest.popStack("%eax", Single!(SizeT));
  dest.call("%eax");
  
  foreach (param; params) {
    dest.sfree(param.valueType().size);
  }
  handleReturn(ret, dest);
}
