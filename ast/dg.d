module ast.dg;

import ast.base, ast.parse, ast.vardecl, ast.namespace, ast.structure,
  ast.pointer, ast.fun;

public import ast.fun: Argument;
class mkDelegate : Expr {
  abstract IType valueType();
  abstract mkDelegate dup();
  Expr ptr, data;
  this(Expr ptr, Expr data) {
    if (ptr.valueType().llvmSize() != "4") {
      logln("unknown size for delegate: ", ptr.valueType(), " ", ptr.valueType().llvmSize());
      fail;
      throw new Exception(Format("Cannot construct delegate from "[], ptr, " (data "[], data, "[])!"[]));
    }
    this.ptr = ptr;
    this.data = data;
  }
  mixin defaultIterate!(ptr, data);
  override Tree collapse() { return this; }
  // ah. comment out until you can fix recursive type preservation fuzz buggy
  /*override Tree collapse() {
    return reinterpret_cast(valueType(), mkTupleValueExprMayDiscard(ptr, data));
  }*/
  override string toString() { return Format("dg(ptr="[], ptr, "[], data="[], data, ")"[]); }
  override void emitLLVM(LLVMFile lf) {
    auto i8ds = save(lf, reinterpret_cast(voidp, data));
    auto i8ps = save(lf, reinterpret_cast(voidp, ptr));
    formTuple(lf, "i8*", i8ps, "i8*", i8ds);
  }
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
    auto ft = fastcast!(FunctionPointer)~ ptr.valueType();
    if (!ft.args.length) fail;
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
      if (!ft.args.length) fail;
      assert(ft.args[$-1].type.llvmSize() == data.valueType().llvmSize());
      cached_type = fastalloc!(Delegate)(ft.ret, ft.args[0..$-1]);
    }
    return cached_type;
  }
}

pragma(set_attribute, C_mkDgConstructExpr, externally_visible);
extern(C) Expr C_mkDgConstructExpr(Expr r, Expr ptrval) {
  return fastalloc!(DgConstructExpr)(r, ptrval);
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

class Delegate_ : Type {
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
    string llvmSize() {
      if (nativePtrSize + nativeIntSize == 8)
        return "8";
      todo("Delegate::llvmSize");
      return null;
    }
    string llvmType() {
      if (nativePtrSize + nativeIntSize == 8)
        return "{i8*, i8*}";
      todo("Delegate::llvmType"); return null;
    }
    string mangle() {
      if (!ret) {
        // throw new Exception("Could not mangle delegate: return type indeterminate");
        logln("Could not mangle delegate: return type indeterminate");
        fail;
      }
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

final class Delegate : Delegate_ {
  static const isFinal = true;
  this() { super(); }
  this(IType ret, Argument[] args) { super(ret, args); }
  this(FunctionType ft) { super(ft); }
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
    cur = ast.tuples.resolveTup(cur);
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

void callDg(LLVMFile lf, IType ret, Expr[] params, Expr dg) {
  auto dgs = collapse(dgAsStruct(dg));
  Expr fun, data;
  if (_is_cheap(dgs, CheapMode.Flatten)) {
    fun  = collapse(mkMemberAccess(dgs, "fun"));
    data = collapse(mkMemberAccess(dgs, "data"));
  } else {
    // logln("dgs = ", dgs, " not cheap to flatten");
    auto dgst = fastalloc!(LLVMValue)(save(lf, dgs), dgs.valueType());
    fun = mkMemberAccess(dgst, "fun");
    data = mkMemberAccess(dgst, "data");
  }
  callFunction(lf, ret, true, false, params ~ data, fun);
}
