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
      fail;
      throw new Exception(Format("Cannot construct delegate from "[], ptr, " (data "[], data, "[])!"[]));
    }
    this.ptr = ptr;
    this.data = data;
  }
  mixin defaultIterate!(ptr, data);
  override string toString() { return Format("dg(ptr="[], ptr, "[], data="[], data, ")"[]); }
  override void emitAsm(AsmFile af) {
    mixin(mustOffset("nativePtrSize * 2"[]));
    // TODO: stack growth order
    data.emitAsm(af);
    ptr.emitAsm(af);
  }
}

static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto dgx = fastcast!(mkDelegate) (it);
    if (!dgx || dgx.classinfo != mkDelegate.classinfo && dgx.classinfo != DgConstructExpr.classinfo) return null;
    return reinterpret_cast(dgx.valueType(), mkTupleExpr(dgx.ptr, dgx.data));
  };
}

import tools.log;
// type-deduced!
class DgConstructExpr : mkDelegate {
  this(Expr fun, Expr base) {
    if (auto dg = fastcast!(Delegate)~ fun.valueType()) {
      assert(false);
      fun = iparse!(Expr, "dg_to_fun"[], "tree.expr"[])("fun.fun"[], "fun"[], fun);
    }
    super(fun, base);
  }
  override DgConstructExpr dup() {
    return fastalloc!(DgConstructExpr)(ptr.dup, data.dup);
  }
  Delegate cached_type;
  override IType valueType() {
    if (!cached_type) {
      auto ft = fastcast!(FunctionPointer)~ ptr.valueType();
      // logln("ptr is "[], ptr, "[], data "[], data, "[], ft "[], ft);
      // logln("ptr type is "[], ptr.valueType());
      assert(ft.args.length);
      assert(ft.args[$-1].type.size == data.valueType().size);
      cached_type = fastalloc!(Delegate)(ft.ret, ft.args[0 .. $-1]);
    }
    return cached_type;
  }
}

// close fp over ptr to dg
Object gotFpCloseExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto fptype = fastcast!(FunctionPointer) (resolveType(ex.valueType()));
    if (!fptype) return null;
    
    if (t2.accept(".toDg("[])) {
      Expr dataptr;
      if (!(rest(t2, "tree.expr"[], &dataptr) && t2.accept(")"[])))
        t2.failparse("Invalid syntax for toDg"[]);
      text = t2;
      return fastalloc!(DgConstructExpr)(ex, dataptr);
    } else return null;
  };
}
mixin DefaultParser!(gotFpCloseExpr, "tree.rhs_partial.fpclose"[], null, null, true);

class Delegate : Type {
  FunctionType ft;
  final IType ret() { return ft.ret; }
  final Argument[] args() { return ft.params; }
  this() { }
  this(IType ret, Argument[] args) { New(ft); ft.ret = ret; ft.params = args; }
  this(FunctionType ft) { this.ft = ft; }
  override {
    bool isComplete() {
      if (!ret || !ret.isComplete) return false;
      foreach (arg; args) if (!arg.type.isComplete) return false;
      return true;
    }
    string toString() {
      if (ret is this) return Format("self delegate "[], args);
      return Format(ret, " delegate "[], args);
    }
    int size() {
      return nativePtrSize * 2;
    }
    string mangle() {
      if (!ret) throw new Exception("Could not mangle delegate: return type indeterminate");
      auto res = "dg_ret_"~((ret is this)?"self":ret.mangle())~"_args";
      if (!args.length) res ~= "_none";
      else foreach (arg; args)
        res ~= "_"~arg.type.mangle();
      return res;
    }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      if (ty is this) return true;
      // break recursion loop
      if (alreadyRecursing(this, ty)) return true;
      pushRecurse(this, ty); scope(exit) popRecurse();
      
      auto dg = fastcast!(Delegate) (resolveType(ty));
      if (!ret || dg && !dg.ret) return false;
      if (!dg || !dg.ret || !ret) { logln(ty); fail; }
      if (dg.ret is ret || (dg.ret is dg && ret is this) || dg.ret == ret) { }
      else return false;
      if (dg.args.length != args.length) return false;
      auto myargs = args();
      foreach (i, arg; dg.args)
        if (!arg.type || !myargs[i].type || arg.type != myargs[i].type) return false;
      return true;
    }
  }
}

IType dgAsStructType(Delegate dgtype) {
  auto res = fastalloc!(Structure)(cast(string) null);
  fastalloc!(RelMember)("fun"[],
    fastalloc!(FunctionPointer)(
      dgtype.ret,
      dgtype.args ~ Argument(voidp)
    ),
    res
  );
  fastalloc!(RelMember)("data"[], voidp, res);
  return res;
}

import ast.casting;
Expr dgAsStruct(Expr ex) {
  auto dgtype = fastcast!(Delegate) (resolveType(ex.valueType()));
  if (!dgtype || dgtype.ft.types_open()) return null;
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
    if (t2.accept("delegate"[]) &&
      t2.gotParlist(list, rest, false)
    ) {
      text = t2;
      return fastalloc!(Delegate)(cur, list);
    } else return null;
  };
}

import ast.assign, ast.fold;
void callDg(AsmFile af, IType ret, Expr[] params, Expr dg) {
  af.comment("Begin delegate call"[]);
  int retsize = ret.size;
  if (Single!(Void) == ret)
    retsize = 0;
  mixin(mustOffset("retsize"[]));
  auto dgs = dgAsStruct(dg);
  mkVar(af, ret, true, (Variable retvar) {
    mixin(mustOffset("0"[]));
    // cheap call - fun ptr is predetermined, no need to lvize the dg
    if (auto sym = fastcast!(Symbol) (optex(mkMemberAccess(dgs, "fun"[])))) {
      params ~= mkMemberAccess(dgs, "data"); opt(params[$-1]);
      callFunction(af, ret, true, false, params, sym);
      if (ret != Single!(Void))
        emitAssign(af, retvar, fastalloc!(Placeholder)(ret), false, true);
    } else {
      int toFree = alignStackFor(dgs.valueType(), af);
      void doit(Variable dgvar) {
        mixin(mustOffset("0"[]));
        params ~= mkMemberAccess(dgvar, "data"); opt(params[$-1]);
        callFunction(af, ret, true, false, params, mkMemberAccess(dgvar, "fun"[]));
        if (ret != Single!(Void))
          emitAssign(af, retvar, fastalloc!(Placeholder)(ret), false, true);
        // Assignment, assuming Placeholder was "really"
        // emitted, has already done this.
        // if (ret != Single!(Void)) af.sfree(ret.size);
      }
      if (auto var = fastcast!(Variable) (dgs)) doit(var);
      else {
        mkVar(af, dgs.valueType(), true, (Variable dgvar) {
          emitAssign(af, dgvar, dgs);
          doit(dgvar);
        });
        af.sfree(dgs.valueType().size);
      }
      af.sfree(toFree);
    }
  });
}
