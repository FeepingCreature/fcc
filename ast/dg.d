module ast.dg;

import ast.base, ast.parse, ast.vardecl, ast.namespace, ast.structure,
  ast.pointer, ast.fun;

public import ast.fun: Argument;
class mkDelegate : Expr {
  abstract IType valueType();
  abstract mkDelegate dup();
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
    if (auto dg = fastcast!(Delegate)~ fun.valueType()) {
      assert(false);
      fun = iparse!(Expr, "dg_to_fun", "tree.expr")("fun.fun", "fun", fun);
    }
    super(fun, base);
  }
  override DgConstructExpr dup() {
    return new DgConstructExpr(ptr, data);
  }
  override IType valueType() {
    auto ft = fastcast!(FunctionPointer)~ ptr.valueType();
    // logln("ptr is ", ptr, ", data ", data, ", ft ", ft);
    // logln("ptr type is ", ptr.valueType());
    assert(ft.args.length);
    assert(ft.args[$-1].type.size == data.valueType().size);
    return new Delegate(ft.ret, ft.args[0 .. $-1]);
  }
}

// close fp over ptr to dg
Object gotFpCloseExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto fptype = fastcast!(FunctionPointer)~ ex.valueType();
    if (!fptype) return null;
    
    if (t2.accept(".toDg(")) {
      Expr dataptr;
      if (!(rest(t2, "tree.expr", &dataptr) && t2.accept(")")))
        t2.failparse("Invalid syntax for toDg");
      text = t2;
      return new DgConstructExpr(ex, dataptr);
    } else return null;
  };
}
mixin DefaultParser!(gotFpCloseExpr, "tree.rhs_partial.fpclose", null, null, true);

class Delegate : Type {
  IType ret;
  Argument[] args;
  this() { }
  this(IType ret, Argument[] args) { this.ret = ret; this.args = args; }
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
        res ~= "_"~arg.type.mangle();
      return res;
    }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      auto dg = fastcast!(Delegate)~ ty;
      if (dg.ret != ret) return false;
      if (dg.args.length != args.length) return false;
      foreach (i, arg; dg.args)
        if (arg.type != args[i].type) return false;
      return true;
    }
  }
}

IType dgAsStructType(Delegate dgtype) {
  auto res = new Structure(null);
  new RelMember("fun",
    new FunctionPointer(
      dgtype.ret,
      dgtype.args ~ Argument(voidp)
    ),
    res
  );
  new RelMember("data", voidp, res);
  return res;
}

import ast.casting;
Expr dgAsStruct(Expr ex) {
  auto dgtype = fastcast!(Delegate)~ ex.valueType();
  if (!dgtype) return null;
  if (auto lv = fastcast!(LValue)~ ex) {
    return new ReinterpretCast!(LValue) (dgAsStructType(dgtype), lv);
  } else {
    return new ReinterpretCast!(Expr) (dgAsStructType(dgtype), ex);
  }
}

static this() {
  implicits ~= &dgAsStruct;
}

// stolen in turn from ast.fun
import ast.tuples;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb rest) {
    IType ptype;
    Argument[] list;
    auto t2 = text;
    if (t2.accept("delegate") &&
      t2.gotParlist(list, rest)
    ) {
      text = t2;
      auto res = new Delegate;
      res.ret = cur;
      res.args = list;
      return res;
    } else return null;
  };
}

import ast.assign;
void callDg(AsmFile af, IType ret, Expr[] params, Expr dg) {
  af.comment("Begin delegate call");
  int retsize = ret.size;
  if (ret == Single!(Void))
    retsize = 0;
  mixin(mustOffset("retsize"));
  auto dgs = dgAsStruct(dg);
  mkVar(af, ret, true, (Variable retvar) {
    mixin(mustOffset("0"));
    mkVar(af, dgs.valueType(), true, (Variable dgvar) {
      mixin(mustOffset("0"));
      (new Assignment(dgvar, dgs)).emitAsm(af);
      params ~= mkMemberAccess(dgvar, "data");
      callFunction(af, ret, true, false, params, mkMemberAccess(dgvar, "fun"));
      if (ret != Single!(Void))
        (new Assignment(retvar, new Placeholder(ret), false, true)).emitAsm(af);
      // Assignment, assuming Placeholder was "really"
      // emitted, has already done this.
      // if (ret != Single!(Void)) af.sfree(ret.size);
    });
    af.sfree(dgs.valueType().size);
  });
}
