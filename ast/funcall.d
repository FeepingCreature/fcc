module ast.funcall;

import ast.fun, ast.base;

alias ast.fun.Argument Argument;

class NamedArg : Expr {
  Expr base;
  string name, reltext;
  this(string name, string text, Expr base) { this.name = name; this.reltext = text; this.base = base; }
  override {
    string toString() { return Format(name, " => ", base); }
    IType valueType() { return base.valueType(); }
    NamedArg dup() { return new NamedArg(name, reltext, base.dup); }
    mixin defaultIterate!(base);
    void emitAsm(AsmFile af) {
      reltext.failparse("Named argument ", name, " could not be assigned to a function call! ");
    }
  }
}

Object gotNamedArg(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!t2.gotIdentifier(name)) return null;
  if (!t2.accept("=>")) return null;
  Expr base;
  if (!rest(t2, "tree.expr", &base))
    t2.failparse("Could not get base expression for named argument '", name, "'");
  auto res = new NamedArg(name, text, base);
  text = t2;
  return res;
}
mixin DefaultParser!(gotNamedArg, "tree.expr.named_arg_1", "115"); // must be high-priority (above arith) to override subtraction.
mixin DefaultParser!(gotNamedArg, "tree.expr.named_arg_2", "221"); // must be below arith too, to be usable in stuff like paren-less calls

bool matchedCallWith(Expr arg, Argument[] params, ref Expr[] res, string info = null, string text = null, bool probe = false, bool exact = false) {
  Expr[string] nameds;
  void removeNameds(ref Iterable it) {
    if (auto ex = fastcast!(Expr)~ it) {
      if (auto tup = fastcast!(AstTuple)~ ex.valueType()) {
        // filter out nameds from the tuple.
        auto exprs = getTupleEntries(ex);
        bool gotNamed;
        foreach (subexpr; exprs) if (auto na = fastcast!(NamedArg) (foldex(subexpr))) {
          gotNamed = true; break;
        }
        if (gotNamed) {
          Expr[] left;
          foreach (subexpr; exprs) {
            auto fs = foldex(subexpr);
            if (auto na = fastcast!(NamedArg) (fs)) {
              nameds[na.name] = na.base;
            } else {
              left ~= fs;
            }
          }
          it = mkTupleExpr(left);
        }
      }
      if (auto na = fastcast!(NamedArg) (ex)) {
        nameds[na.name] = na.base;
        it = mkTupleExpr();
      }
    }
  }
  {
    Iterable forble = arg;
    removeNameds(forble);
    void checkNameds(ref Iterable it) {
      /*logln("<", (cast(Object) it).classinfo.name, ">");
      if (auto rce = fastcast!(RCE) (it)) {
        logln(" - ", rce.to);
      }*/
      if (auto na = fastcast!(NamedArg) (it)) {
        // asm { int 3; }
        throw new Exception(Format("Nested named-arg found! :( ", na));
      }
      it.iterate(&checkNameds);
      // logln("</", (cast(Object) it).classinfo.name, ">");
    }
    checkNameds(forble);
    arg = fastcast!(Expr)~ forble;
  }
  
  Expr[] args;
  args ~= arg;
  Expr[] flatten(Expr ex) {
    if (fastcast!(AstTuple)~ ex.valueType())
      return getTupleEntries(ex);
    else
      return null;
  }
  int flatLength(Expr ex) {
    int res;
    if (fastcast!(AstTuple)~ ex.valueType()) {
      foreach (entry; getTupleEntries(ex))
        res += flatLength(entry);
    } else {
      res ++;
    }
    return res;
  }
  int flatArgsLength() {
    int res;
    foreach (arg; args) res += flatLength(arg);
    return res;
  }
  foreach (i, tuple; params) {
    auto type = tuple.type, name = tuple.name;
    type = resolveType(type);
    if (cast(Variadic) type) {
      foreach (ref rest_arg; args)
        if (!gotImplicitCast(rest_arg, (IType it) { return !fastcast!(StaticArray) (it); }))
          throw new Exception(Format("Invalid argument to variadic: ", rest_arg));
      res ~= args;
      args = null;
      break;
    }
    {
      IType[] tried;
      if (auto p = name in nameds) {
        auto ex = *p, backup = ex;
        nameds.remove(name);
        if (exact) {
          if (ex.valueType() != type)
            if (probe)
              return false;
            else
              text.failparse("Couldn't match named argument ", name, " of ", backup.valueType(), " exactly to function call '", info, "', ", type, ".");
        } else {
          if (!gotImplicitCast(ex, type, (IType it) { tried ~= it; return test(it == type); }))
            if (probe)
              return false;
            else
              text.failparse("Couldn't match named argument ", name, " of ", backup.valueType(), " to function call '", info, "', ", type, "; tried ", tried, ".");
        }
        res ~= ex;
        continue;
      }
    }
    if (!flatArgsLength()) {
      if (tuple.initEx) {
        auto ex = tuple.initEx;
        IType[] tried;
        if (exact) {
          if (ex.valueType() != type)
            if (probe)
              return false;
            else
              text.failparse("Couldn't match default argument for ", name, ": ", tuple.initEx.valueType(), " exactly to ", type, ".");
        } else {
          if (!gotImplicitCast(ex, type, (IType it) { tried ~= it; return test(it == type); }))
            if (probe)
              return false;
            else
              text.failparse("Couldn't match default argument for ", name, ": ", tuple.initEx.valueType(), " to ", type,"; tried ", tried, ".");
        }
        res ~= ex;
        continue;
      }
      if (probe) return false;
      if (text)
        text.failparse("Not enough parameters for '", info, "'; left over ", type, "!");
      logln("Not enough parameters for '", info, "'; left over ", type, "!");
      asm { int 3; }
    }
  retry:
    auto ex = args.take();
    auto backup = ex;
    IType[] tried;
    
    ex = foldex(ex);
    
    if (exact ? (ex.valueType() != type) : !gotImplicitCast(ex, type, (IType it) {
      tried ~= it;
      // logln(" !! is ", it, " == ", type, "? ", test(it == type));
      return test(it == type);
    })) {
      Expr[] list;
      if (gotImplicitCast(ex, (IType it) { return !!fastcast!(Tuple) (it); }) && (list = flatten(ex), !!list)) {
        args = list ~ args;
        goto retry;
      } else {
        if (probe) return false;
        text.failparse("Couldn't match ", backup.valueType(), " to function call '", info, "', ", params[i], " (", i, "); tried ", tried);
      }
    }
    res ~= ex;
  }
  Expr[] flat;
  void recurse(Expr ex) {
    if (fastcast!(AstTuple)~ ex.valueType())
      foreach (entry; flatten(ex)) recurse(entry);
    else flat ~= ex;
  }
  foreach (arg2; args) recurse(arg2);
  if (flat.length) {
    // logln("flattened to ", flat);
    // text.failparse("Extraneous parameters to '", info, "' of ", params, ": ", args);
    text.setError("Extraneous parameters to '", info, "' of ", params, ": ", args);
    return false;
  }
  if (nameds.length) {
    throw new Exception(Format("Leftover named arguments: ", nameds));
  }
  return true;
}

bool cantBeCall(string s) {
  return s.accept(".");
}

import ast.properties;
import ast.tuple_access, ast.tuples, ast.casting, ast.fold, ast.tuples: AstTuple = Tuple;
bool matchCall(ref string text, string info, Argument[] params, ParseCb rest, ref Expr[] res, bool test, bool precise) {
  Expr arg;
  auto backup_text = text; 
  if (!backup_text.length) return false; // wat
  // speed opt - a call can only begin
  // with one of those separating tokens
  const string valid_call_start_tokens = "( \r\n\t-";
  bool token_match;
  foreach (ch; valid_call_start_tokens)
    if (text.startsWith([ch])) { token_match = true; break; }
  if (!token_match) return false;
  
  bool isTuple;
  {
    auto t2 = text;
    if (t2.accept("(")) isTuple = true;
  }
  
  // Only do this if we actually expect a tuple _literal_
  // properties on tuple _variables_ are valid!
  auto backup = *propcfg.ptr();
  scope(exit) *propcfg.ptr() = backup;
  if (isTuple) propcfg().withTuple = false;
    
  if (!rest(text, "tree.expr _tree.expr.arith", &arg)) {
    return false;
  }
  return matchedCallWith(arg, params, res, info, backup_text, test, precise);
}

Expr buildFunCall(Function fun, Expr arg, string info) {
  auto fc = fun.mkCall();
  if (!matchedCallWith(arg, fun.getParams(), fc.params, info))
    return null;
  return fc;
}

import ast.parse, ast.static_arrays;
Object gotCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    if (t2.cantBeCall()) return null;
    Function fun;
    if (auto f = fastcast!(Function) (obj)) {
      fun = f;
    } else if (auto os = fastcast!(OverloadSet) (obj)) {
      bool precise = true;
      retry_match:
      Function[] candidates;
      typeof(fun.getParams())[] parsets, candsets;
      foreach (osfun; os.funs) {
        auto t3 = t2;
        if (matchCall(t3, osfun.name, osfun.getParams(), rest, osfun.mkCall().params, true, precise)) {
          candidates ~= osfun;
          candsets ~= osfun.getParams();
        }
        parsets ~= osfun.getParams();
      }
      if (!candidates) {
        if (precise) { precise = false; goto retry_match; } // none _quite_ match .. 
        t2.failparse("Unable to call '", os.name, "': matched none of ", parsets);
      }
      if (candidates.length > 1) {
        t2.failparse("Unable to call '", os.name,
          "': ambiguity between ", candsets);
      }
      fun = candidates[0];
    } else return null;
    auto fc = fun.mkCall();
    auto params = fun.getParams();
    resetError();
    if (!matchCall(t2, fun.name, params, rest, fc.params, false, false)) {
      if (t2.accept("("))
        text.failparse("Failed to call function: ", error()._1);
      auto t3 = t2;
      // valid call terminators
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
  this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(fp, params);
  override void emitAsm(AsmFile af) {
    auto fntype = fastcast!(FunctionPointer)~ fp.valueType();
    callFunction(af, fntype.ret, true, fntype.stdcall, params, fp);
  }
  override IType valueType() {
    return (fastcast!(FunctionPointer)~ fp.valueType()).ret;
  }
}

Object gotFpCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    if (t2.cantBeCall()) return null;

    FunctionPointer fptype;
    if (!gotImplicitCast(ex, (IType it) { fptype = fastcast!(FunctionPointer) (it); return !!fptype; }))
      return null;
    
    auto fc = new FpCall;
    fc.fp = ex;
    
    if (!matchCall(t2, Format("delegate ", ex), fptype.args, rest, fc.params, false, false))
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
    auto dgtype = fastcast!(Delegate)~ dg.valueType();
    callDg(af, dgtype.ret, params, dg);
  }
  override IType valueType() {
    return (fastcast!(Delegate)~ dg.valueType()).ret;
  }
}

Object gotDgCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    if (t2.cantBeCall()) return null;
    
    Delegate dgtype;
    if (!gotImplicitCast(ex, (IType it) { dgtype = fastcast!(Delegate) (it); return !!dgtype; }))
      return null;
    
    auto dc = new DgCall;
    dc.dg = ex;
    if (!matchCall(t2, Format("delegate ", ex), dgtype.args, rest, dc.params, false, false))
      return null;
    text = t2;
    return dc;
  };
}
mixin DefaultParser!(gotDgCallExpr, "tree.rhs_partial.dgcall");

import ast.literal_string, ast.modules;

static this() {
  // allow use of .replace in mixins
  foldopt ~= delegate Itr(Itr it) {
    auto fc = fastcast!(FunCall) (it);
    if (!fc) return null;
    if (fc.fun.name != "replace" /or/ "[wrap]replace") return null;
    auto smod = fastcast!(Module) (fc.fun.sup);
    if (!smod || !sysmod || smod !is sysmod) return null;
    auto args = fc.getParams();
    assert(args.length == 3);
    string[3] str;
    foreach (i, arg; args) {
      arg = foldex(arg);
      if (auto se = fastcast!(StringExpr) (arg)) str[i] = se.str;
      else {
        // logln("couldn't fold properly because arg was ", arg);
        // asm { int 3; }
        return null;
      }
    }
    return new StringExpr(str[0].replace(str[1], str[2]));
  };
}

// helper for ast.fun
extern(C) void funcall_emit_fun_end_guard(AsmFile af, string name) {
  (new ExprStatement(buildFunCall(
    fastcast!(Function) (sysmod.lookup("missed_return")),
    mkTupleExpr(new StringExpr(name)),
    "missed return signal"
  ))).emitAsm(af);
}
