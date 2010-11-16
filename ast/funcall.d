module ast.funcall;

import ast.fun, ast.base;

void matchCallWith(Expr arg, IType[] params, ref Expr[] res, string info = null, string text = null) {
  Expr[] args;
  args ~= arg;
  Expr[] flatten(Expr ex) {
    if (cast(AstTuple) ex.valueType())
      return getTupleEntries(ex);
    else
      return null;
  }
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
      throw new Exception(Format("Not enough parameters for '", info, "'; left over ", type, "!"));
    }
    IType[] tried;
  retry:
    auto ex = args.take();
    auto backup = ex;
    
    if (!gotImplicitCast(ex, type, (IType it) {
      tried ~= it;
      return test(it == type);
    })) {
      Expr[] list;
      if (gotImplicitCast(ex, (IType it) { return !!cast(Tuple) it; }) && (list = flatten(ex), !!list)) {
        args = list ~ args;
        goto retry;
      } else
        text.failparse("Couldn't match ", backup.valueType(), " to function call ", info, ", ", params[i], " (", i, "); tried ", tried);
    }
    res ~= ex;
  }
  Expr[] flat;
  void recurse(Expr ex) {
    if (cast(AstTuple) ex.valueType())
      foreach (entry; flatten(ex)) recurse(entry);
    else flat ~= ex;
  }
  foreach (arg2; args) recurse(arg2);
  if (flat.length) {
    logln("flattened to ", flat);
    text.failparse("Extraneous parameters to '", info, "' of ", params, ": ", args);
  }
}

import ast.tuple_access, ast.tuples, ast.casting, ast.fold, ast.tuples: AstTuple = Tuple;
bool matchCall(ref string text, string info, IType[] params, ParseCb rest, ref Expr[] res) {
  Expr arg;
  auto backup_text = text; 
  if (!backup_text.length) return false; // wat
  // speed opt - a call can only begin
  // with one of those separating tokens
  const string valid_call_start_tokens = "({[ ";
  bool token_match;
  foreach (ch; valid_call_start_tokens)
    if (text.startsWith([ch])) { token_match = true; break; }
  if (!token_match) return false;
  if (!rest(text, "tree.expr _tree.expr.arith >tree.expr.properties.tup", &arg)) {
    return false;
  }
  matchCallWith(arg, params, res, info, backup_text);
  return true;
}

Expr buildFunCall(Function fun, Expr arg) {
  auto fc = fun.mkCall();
  IType[] params;
  foreach (entry; fun.type.params) params ~= entry._0;
  matchCallWith(arg, params, fc.params);
  return fc;
}

import ast.parse, ast.static_arrays;
Object gotCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Function fun) {
    auto fc = fun.mkCall();
    IType[] params;
    foreach (entry; fun.type.params) params ~= entry._0;
    if (!matchCall(t2, fun.name, params, rest, fc.params)) {
      auto t3 = t2;
      if (params.length || !t3.accept(";"))
        return null;
    }
    text = t2;
    return fc;
  };
}
mixin DefaultParser!(gotCallExpr, "tree.rhs_partial.funcall");

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
mixin DefaultParser!(gotFpCallExpr, "tree.rhs_partial.fpcall");

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
mixin DefaultParser!(gotDgCallExpr, "tree.rhs_partial.dgcall");
