module ast.funcall;

import ast.fun, ast.base, ast.vardecl, ast.aggregate, ast.structure, ast.namespace;

alias ast.fun.Argument Argument;

class NamedArg : Expr {
  Expr base;
  string name, reltext;
  this(string name, string text, Expr base) { this.name = name; this.reltext = text; this.base = base; }
  override {
    string toString() { return Format(name, " => "[], base); }
    IType valueType() { return base.valueType(); }
    NamedArg dup() { return fastalloc!(NamedArg)(name, reltext, base.dup); }
    mixin defaultIterate!(base);
    void emitLLVM(LLVMFile lf) {
      reltext.failparse("Named argument ", name, " could not be assigned to a function call! ");
    }
  }
}

IType[] relevant(IType[] array) {
  IType[] res;
  foreach (it; array)
    if (!Format(it).startsWith("fpos of a"[])) res ~= it;
  return res;
}

Object gotNamedArg(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  Expr base;
  if (t2.accept("=>")) { // named flag
    if (!t2.gotIdentifier(name))
      t2.failparse("Flag expected");
    base = fastcast!(Expr) (sysmod.lookup("true"));
  } else {
    if (!t2.gotIdentifier(name)) return null;
    if (!t2.accept("=>")) return null;
    if (!rest(t2, "tree.expr"[], &base))
      t2.failparse("Could not get base expression for named argument '", name, "'");
  }
  auto res = fastalloc!(NamedArg)(name, text, base);
  text = t2;
  return res;
}
mixin DefaultParser!(gotNamedArg, "tree.expr.named_arg_1", "115"); // must be high-priority (above arith) to override subtraction.
mixin DefaultParser!(gotNamedArg, "tree.expr.named_arg_2", "221"); // must be below arith too, to be usable in stuff like paren-less calls

bool matchedCallWith(Expr arg, Argument[] params, ref Expr[] res, out Statement[] inits, lazy string info, string text = null, bool probe = false, bool exact = false, int* scorep = null) {
  Expr[string] nameds;
  bool changed;
  void removeNameds(ref Iterable it) {
    // logln("removeNameds <", fastcast!(Object)(it).classinfo.name, " ", it, ">");
    if (fastcast!(Variable) (it)) return;
    if (auto ex = fastcast!(Expr)~ it) {
      auto tup = fastcast!(AstTuple) (ex.valueType());
      if (tup) {
        bool canHaveNameds = true;
        if (fastcast!(StatementAndExpr) (ex)) canHaveNameds = false;
        if (canHaveNameds) {
          // filter out nameds from the tuple.
          auto exprs = getTupleEntries(ex, null, true);
          bool gotNamed;
          
          bool backup = changed;
          changed = false;
          scope(exit) changed = backup;
          
          foreach (ref subexpr; exprs) {
            opt(subexpr);
            auto sit = fastcast!(Iterable) (subexpr);
            removeNameds(sit);
            subexpr = fastcast!(Expr) (sit);
          }
          foreach (i, ref subexpr; exprs) {
            if (fastcast!(NamedArg) (subexpr)) {
              gotNamed = true;
              break;
            }
          }
          Expr[] left;
          foreach (i, subexpr; exprs) {
            if (auto na = fastcast!(NamedArg) (subexpr)) {
              changed = true;
              nameds[na.name] = na.base;
            } else if (subexpr.valueType() != mkTuple()) {
              left ~= subexpr;
            } else changed = true;
          }
          exprs = left;
          if (changed) it = mkTupleExpr(exprs);
          changed = false;
        }
      }
      if (auto na = fastcast!(NamedArg) (ex)) {
        changed = true;
        nameds[na.name] = na.base;
        it = mkTupleExpr();
      }
    }
  }
  {
    Iterable forble = arg;
    removeNameds(forble);
    void checkNameds(ref Iterable it) {
      if (fastcast!(Variable) (it)) return;
      if (fastcast!(FunCall) (it)) return;
      /*logln("<", (cast(Object) it).classinfo.name, ">");
      if (auto rce = fastcast!(RCE) (it)) {
        logln(" - ", rce.to);
      }*/
      if (auto na = fastcast!(NamedArg) (it)) {
        // fail;
        throw new Exception(Format("Leftover named-arg found! ", na, " (couldn't remove)"));
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
    if (fastcast!(AstTuple)~ ex.valueType()) {
      Statement st;
      auto res = getTupleEntries(ex, &st);
      if (st) inits ~= st;
      return res;
    } else {
      return null;
    }
  }
  int flatLength(Expr ex) {
    int res;
    if (fastcast!(AstTuple)~ ex.valueType()) {
      foreach (entry; getTupleEntries(ex, null, true))
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
    if (fastcast!(Variadic) (type)) {
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
              text.failparse("Couldn't match named argument ", name, " of ", backup.valueType(), " exactly to function call '", info(), "', ", type, ".");
        } else {
          if (!gotImplicitCast(ex, type, (IType it) { tried ~= it; return test(it == type); }, false))
            if (probe)
              return false;
            else
              text.failparse("Couldn't match named argument ", name, " of ", backup.valueType(), " to function call '", info(), "', ", type, "; tried ", tried, ".");
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
          if (!gotImplicitCast(ex, type, (IType it) { tried ~= it; return test(it == type); }, false))
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
        text.failparse("Not enough parameters for '", info(), "'; left over ", type, "!");
      logln("Not enough parameters for '", info(), "'; left over ", type, "!");
      fail;
    }
    IType[] tried;
  retry:
    auto ex = args.take();
    auto backup = ex;
    
    opt(ex);
    
    int score;
    
    if (exact ? (ex.valueType() != type) : !gotImplicitCast(ex, type, (IType it) {
      tried ~= it;
      // logln(" !! is ", it, " == ", type, "? ", test(it == type));
      return test(it == type);
    }, false, &score)) {
      Expr[] list;
      if (gotImplicitCast(ex, Single!(HintType!(Tuple)), (IType it) { return !!fastcast!(Tuple) (it); }) && (list = flatten(ex), !!list)) {
        args = list ~ args;
        goto retry;
      } else {
        if (probe) return false;
        string formatlines(IType[] types) {
          string res;
          foreach (i, type; types)
            res ~= qformat(" ", i, ": ", type, "\n");
          if (!res) res = " none\n";
          res = res[0..$-1];
          return res;
        }
        text.failparse("Couldn't match\n",
          "  ", backup.valueType(), "\n",
          "to function call '", info(), "' (", i, "):\n"
          "  ", params[i], "\n",
          "tried:\n", formatlines(relevant(tried)));
      }
    }
    if (scorep) *scorep += score;
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
    IType[] types;
    foreach (a; flat) types ~= a.valueType();
    // text.failparse("Extraneous parameters to '", info(), "' of ", params, ": ", types);
    text.setError("Extraneous parameters to '"[], info(), "' of "[], params, ": "[], types);
    return false;
  }
  if (nameds.length) {
    string fninfo = info();
    if (!fninfo) fninfo = "function";
    throw new Exception(Format(fninfo, " has no arguments named "[], nameds.keys));
  }
  return true;
}

bool cantBeCall(string s) {
  // brackets are always implicit terminators. this prevents the ugliness of };
  // if (s.hadABracket()) return true;
  auto s2 = s;
  if (s2.hadABracket()) {
    while (s2.length && s2[0] == ' ') s2 = s2[1..$];
    if (s2.length && (s2[0] == '\r' || s2[0] == '\n')) return true;
  }
  return s.accept(".") || s.accept("{");
}

import ast.properties;
import ast.tuple_access, ast.tuples, ast.casting, ast.fold, ast.tuples: AstTuple = Tuple;
bool matchCall(ref string text, lazy string lazy_info, Argument[] params, ParseCb rest, ref Expr[] res, out Statement[] inits, bool test, bool precise, bool allowAutoCall, int* scorep = null) {
  string infocache;
  string info() { if (!infocache) infocache = lazy_info(); return infocache; }
  
  int neededParams;
  foreach (par; params) if (!par.initEx) neededParams ++;
  if (!neededParams) {
    auto t2 = text;
    // paramless call
    if (t2.accept(";")) return true;
  }
  Expr arg;
  auto backup_text = text; 
  if (!backup_text.length) return false; // wat
  
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
  
  {
    auto t2 = text;
    
    if (!rest(t2, "tree.expr.cond.other"[], &arg) && !rest(t2, "tree.expr _tree.expr.arith"[], &arg)) {
      if (params.length) return false;
      else if (info().startsWith("delegate"[])) return false;
      else if (allowAutoCall) arg = mkTupleExpr();
      else return false;
    }
    if (!matchedCallWith(arg, params, res, inits, info(), backup_text, test, precise, scorep)) return false;
    text = t2;
    return true;
  }
}

extern(C) Expr _buildFunCall(Object obj, Expr arg, string info) {
  auto fun = fastcast!(Function) (obj);
  if (!fun) {
    logln("you want me to call a ", obj, "?");
    fail;
  }
  auto fc = fun.mkCall();
  Statement[] inits;
  if (!matchedCallWith(arg, fun.getParams(false), fc.params, inits, info))
    return null;
  if (!inits.length) return fc;
  else if (inits.length > 1) inits = [fastalloc!(AggrStatement)(inits)];
  return mkStatementAndExpr(inits[0], fc);
}

import ast.parse, ast.static_arrays;
Object gotCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    if (t2.cantBeCall()) return null;
    // is this an expr that has alternatives? ie. is it okay to maybe return null here?
    bool exprHasAlternativesToACall;
    auto oobj = obj;
    if (auto nobj = getOpCall(obj)) { exprHasAlternativesToACall = true; obj = nobj; }
    Function fun;
    if (auto f = fastcast!(Function) (obj)) {
      fun = f;
    } else if (auto os = fastcast!(OverloadSet) (obj)) {
      bool precise = true;
      retry_match:
      Function[] candidates;
      typeof(fun.getParams(false))[] parsets, candsets;
      int[] scores;
      foreach (osfun; os.funs) {
        auto t3 = t2;
        Statement[] inits;
        // logln(t3.nextText(), ": consider ", osfun);
        int score;
        if (matchCall(t3, osfun.name, osfun.getParams(false), rest, osfun.mkCall().params, inits, true, precise, !exprHasAlternativesToACall, &score)) {
          candidates ~= osfun;
          candsets ~= osfun.getParams(false);
          scores ~= score;
        }
        parsets ~= osfun.getParams(false);
      }
      if (!candidates) {
        if (precise) { precise = false; goto retry_match; } // none _quite_ match ..
        if (exprHasAlternativesToACall) return null;
        t2.failparse("Unable to call '", os.name, "': matched none of ", parsets);
      }
      if (candidates.length > 1) {
        // try to select the expr with the lowest score
        int lowest = int.max;
        foreach (score; scores) if (score < lowest) lowest = score;
        // exclude candidates with larger scores
        auto backup = candidates, scores_backup = scores;
        candidates = null; scores = null;
        foreach (i, score; scores_backup) if (score == lowest) {
          candidates ~= backup[i];
          scores ~= score;
        }
      }
      if (candidates.length > 1) {
        t2.failparse("Unable to call '", os.name,
          "': ambiguity between ", candsets, " btw ", os.funs, " of score ", scores[0]);
      }
      fun = candidates[0];
    } else return null;
    auto fc = fun.mkCall();
    auto params = fun.getParams(false);
    resetError();
    bool result;
    Statement[] inits;
    Expr res = fc;
    auto t4 = t2;
    try {
      result = matchCall(t2, fun.name, params, rest, fc.params, inits, false, false, !exprHasAlternativesToACall);
      if (inits.length > 1) inits = [fastalloc!(AggrStatement)(inits)];
      if (inits.length) res = mkStatementAndExpr(inits[0], foldex(fc));
      else res = foldex(res);
    }
    catch (ParseEx pe) text.failparse("cannot call: ", pe);
    catch (Exception ex) text.failparse("cannot call: ", ex);
    if (!result) {
      if (t2.accept("("))
        t2.failparse("Failed to call function with ", params);
      auto t3 = t2;
      int neededParams;
      foreach (param; params) if (!param.initEx) neededParams ++;
      if (neededParams || !t3.acceptTerminatorSoft()) {
        t2.failparse("Failed to build paramless call");
      }
    }
    text = t2;
    return fastcast!(Object) (res);
  };
}
mixin DefaultParser!(gotCallExpr, "tree.rhs_partial.funcall");

class FpCall : Expr {
  Expr fp;
  Expr[] params;
  this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(fp, params);
  override void emitLLVM(LLVMFile lf) {
    auto fntype = fastcast!(FunctionPointer)~ fp.valueType();
    callFunction(lf, fntype.ret, true, fntype.stdcall, params, fp);
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
    if (!gotImplicitCast(ex, Single!(HintType!(FunctionPointer)), (IType it) { fptype = fastcast!(FunctionPointer) (it); return !!fptype; }))
      return null;
    
    auto fc = new FpCall;
    fc.fp = ex;
    
    Statement[] inits;
    if (!matchCall(t2, Format("delegate "[], ex.valueType()), fptype.args, rest, fc.params, inits, false, false, false))
      return null;
    
    text = t2;
    Expr res = fc;
    if (inits.length > 1) inits = [fastalloc!(AggrStatement)(inits)];
    if (inits.length) res = mkStatementAndExpr(inits[0], res);
    return fastcast!(Object) (res);
  };
}
mixin DefaultParser!(gotFpCallExpr, "tree.rhs_partial.fpcall");

import ast.dg;
class DgCall : Expr {
  Expr dg;
  Expr[] params;
  mixin DefaultDup!();
  mixin defaultIterate!(dg, params);
  override void emitLLVM(LLVMFile lf) {
    auto dgtype = fastcast!(Delegate) (resolveType(dg.valueType()));
    callDg(lf, dgtype.ret, params, dg);
  }
  override IType valueType() {
    return (fastcast!(Delegate) (resolveType(dg.valueType()))).ret;
  }
  override string toString() {
    return qformat(dg, "("[], params, ")"[]);
  }
}

Object gotDgCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    if (t2.cantBeCall()) return null;
    
    Delegate dgtype;
    if (!gotImplicitCast(ex, Single!(HintType!(Delegate)), (IType it) { dgtype = fastcast!(Delegate) (it); return !!dgtype; }))
      return null;
    
    auto dc = new DgCall;
    dc.dg = ex;
    Statement[] inits;
    if (!matchCall(t2, Format("delegate "[], ex.valueType()), dgtype.args, rest, dc.params, inits, false, false, false))
      return null;
    text = t2;
    Expr res = dc;
    if (inits.length > 1) inits = [fastalloc!(AggrStatement)(inits)];
    if (inits.length) res = mkStatementAndExpr(inits[0], res);
    return fastcast!(Object) (res);
  };
}
mixin DefaultParser!(gotDgCallExpr, "tree.rhs_partial.fpz_dgcall"); // put this after fpcall

import ast.literal_string, ast.modules;

static this() {
  // allow use of .replace in mixins
  foldopt ~= delegate Itr(Itr it) {
    auto fc = fastcast!(FunCall) (it);
    if (!fc) return null;
    if (fc.fun.name != "replace"[] /or/ "[wrap]replace"[]) return null;
    auto smod = fastcast!(Module) (fc.fun.sup);
    if (!smod || !sysmod || smod !is sysmod) return null;
    auto args = fc.getParams();
    if (args.length != 3) {
      logln("wrong number of args found: ", fc, " - ", args);
      fail;
    }
    string[3] str;
    foreach (i, arg; args) {
      if (auto se = fastcast!(StringExpr) (arg)) str[i] = se.str;
      else {
        // logln("couldn't fold properly because arg was ", arg);
        // fail;
        return null;
      }
    }
    return fastalloc!(StringExpr)(str[0].replace(str[1], str[2]));
  };
}

// helper for ast.fun
extern(C) void funcall_emit_fun_end_guard(LLVMFile lf, string name) {
  (fastalloc!(ExprStatement)(buildFunCall(
    sysmod.lookup("missed_return"),
    fastalloc!(StringExpr)(name),
    "missed return signal"
  ))).emitLLVM(lf);
}
