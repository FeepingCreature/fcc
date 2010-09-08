module ast.funcall;

import ast.fun, ast.base;

import ast.tuple_access, ast.casting, ast.fold, ast.tuples: AstTuple = Tuple;
bool matchCall(ref string text, string info, IType[] params, ParseCb rest, ref Expr[] res) {
  Expr arg;
  if (!rest(text, "tree.expr _tree.expr.arith", &arg))
    return false;
  Expr[] args;
  void flatten(Expr ex) {
    if (cast(AstTuple) ex.valueType()) {
      foreach (entry; getTupleEntries(ex))
        flatten(entry);
    } else args ~= fold(ex);
  }
  flatten(arg);
  foreach (i, type; params) {
    if (cast(Variadic) type) {
      foreach (ref rest_arg; args)
        if (!gotImplicitCast(rest_arg, (IType it) { return !cast(StaticArray) it; }))
          throw new Exception(Format("Invalid argument to variadic: ", rest_arg));
      res ~= args;
      args = null;
      break;
    }
    if (!args.length) {
      throw new Exception(Format("Not enough parameters for ", info, "!"));
    }
    auto ex = args.take();
    auto backup = ex;
    IType[] tried;
    if (!gotImplicitCast(ex, (IType it) {
      tried ~= it;
      return test(it == type);
    }))
      throw new Exception(Format("Couldn't match ", backup.valueType(), " to function call ", info, " ", params, "[", i, "]; tried ", tried, ". "));
    res ~= ex;
  }
  if (args.length) {
    throw new Exception(Format("Extraneous parameters to ", info, ": ", args));
  }
  return true;
}

import ast.parse, ast.static_arrays;
Object gotCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Function fun) {
    auto fc = fun.mkCall();
    IType[] params;
    foreach (entry; fun.type.params) params ~= entry._0;
    if (!matchCall(t2, fun.name, params, rest, fc.params))
      return null;
    text = t2;
    return fc;
  };
}
mixin DefaultParser!(gotCallExpr, "tree.rhs_partial.funcall", null, true);

class FpCall : Expr {
  Expr fp;
  Expr[] params;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(params);
  override void emitAsm(AsmFile af) {
    auto fntype = cast(FunctionPointer) fp.valueType();
    callFunction(af, fntype.ret, params, fp);
  }
  override IType valueType() {
    return (cast(FunctionPointer) fp.valueType()).ret;
  }
}

Object gotFpCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto fptype = cast(FunctionPointer) ex.valueType();
    if (!fptype) return null;
    
    auto fc = new FpCall;
    fc.fp = ex;
    
    if (!matchCall(t2, Format("delegate ", ex), fptype.args, rest, fc.params))
      return null;
    
    text = t2;
    return fc;
  };
}
mixin DefaultParser!(gotFpCallExpr, "tree.rhs_partial.fpcall", null, true);

import ast.dg;
class DgCall : Expr {
  Expr dg;
  Expr[] params;
  mixin DefaultDup!();
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
    if (!matchCall(t2, Format("delegate ", ex), dgtype.args, rest, dc.params))
      return null;
    text = t2;
    return dc;
  };
}
mixin DefaultParser!(gotDgCallExpr, "tree.rhs_partial.dgcall", null, true);
