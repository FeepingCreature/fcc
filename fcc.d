module fcc; // feep's crazed compiler
// fcc is licensed under the terms of the GNU General Public License v3 or GPLv3.

import tools.log, tools.compat, tools.smart_import;
alias ast.types.Type Type;
import classgraph;
static import std.gc;

mixin(expandImport(`ast.[
  aggregate_parse, returns, ifstmt, loops, assign,
  structure, variable, fun, unary, arrays, index, slice,
  nestfun, structfuns, type_info, aliasing, oop, dg,
  newexpr, guard, withstmt, templ, globvars, context,
  concat, stringex, c_bind, eval, iterator, iterator_ext, properties,
  tuples, tuple_access, literal_string, literals, funcall, vector, externs,
  intr, conditionals, opers, conditional_opt, cond, casting,
  pointer, nulls, sa_index_opt, intrinsic, mode, repl,
  propcall, properties_parse, main, alignment, modules_parse,
  platform, math, longmath, base, mixins, int_literal, static_arrays,
  enums, import_parse, pragmas, trivial, fp, expr_statement,
  typeset, dependency, prefixfun,
  macros, tenth, vardecl_expr, vardecl_parse, property, condprop],
  casts, llvmtype, cache`));

alias ast.tuples.resolveTup resolveTup;
alias ast.c_bind.readback readback;
// placed here to resolve circular dependency issues
import ast.parse, ast.namespace, ast.scopes;
// from ast.modules_parse
mixin DefaultParser!(gotNamed, "tree.expr.named", "24");

const ProgbarLength = 60;

string output;

bool sigmode;

string my_prefix() {
  version(Windows) { return path_prefix; }
  else return path_prefix ~ platform_prefix;
}

string[] linkerArgs;

string[] processCArgs(string[] ar) {
  string[] res;
  while (ar.length) {
    auto arg = ar.take();
    if (arg == "-pthread") continue; // silently ignore;
    if (arg.startsWith("-D")) continue;
    if (auto rest = arg.startsWith("-l").strip()) {
      if (!rest.length) rest = ar.take();
      linkerArgs ~= "-l"~rest;
      continue;
    }
    if (auto rest = arg.startsWith("-L").strip()) {
      if (!rest.length) rest = ar.take();
      linkerArgs ~= "-L"~rest;
      continue;
    }
    if (auto rest = arg.startsWith("-Wl")) {
      rest.accept(",");
      rest = rest.strip();
      if (!rest.length) rest = ar.take();
      linkerArgs ~= rest;
      continue;
    }
    if (auto rest = arg.startsWith("-I")) {
      rest = rest.strip();
      if (!rest.length) rest = ar.take();
      include_path = rest ~ include_path;
      continue;
    }
    res ~= arg;
  }
  return res;
}

string[Tree] ids;

pragma(set_attribute, mangletree, externally_visible);
extern(C) string mangletree(Tree tr) {
  if (auto ea = fastcast!(ExprAlias)(tr))
    return "ea_"~mangletree(ea.base);
  if (auto rce = fastcast!(RCE)(tr))
    return "rce_"~rce.to.mangle()~"_"~mangletree(rce.from);
  if (auto ie = fastcast!(IntExpr)(tr))
    return qformat("ie_", ie.num);
  if (auto se = fastcast!(StringExpr)(tr))
    return qformat("se_", cleanup(se.str));
  synchronized {
    if (auto p = tr in ids) return *p;
    auto res = qformat("uniquetree_", ids.length);
    ids[tr] = res;
    return res;
  }
  logln("tr: ", fastcast!(Object)(tr).classinfo.name, " ", tr);
  asm { int 3; }
}

static this() {
  setupSlice();
  setupIndex();
  setupIterIndex();
  setupConditionalOpt();
  pragmas["fast"] = delegate Object(Expr ex) {
    if (ex) throw new Exception("pragma 'fast' does not take arguments");
    auto fun = namespace().get!(Function);
    if (!fun) throw new Exception("pragma 'fast' must be inside a function");
    fun.optimize = true;
    releaseMode = true; // it'll be restored at the end of the function - no harm
    return Single!(NoOp);
  };
  // Link with this library
  bool isStringLiteral(Expr ex) { return !!fastcast!(StringExpr) (foldex(ex)); }
  pragmas["lib"] = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, &isStringLiteral))
      throw new Exception("Lib name expected. ");
    string str = (fastcast!(StringExpr) (foldex(ex))).str;
    string newarg = "-l" ~ str;
    // only add once .. becomes relevant in incremental mode
    foreach (arg; extra_linker_args) if (arg == newarg) {
      newarg = null;
      break;
    }
    if (newarg) extra_linker_args = newarg ~ extra_linker_args;
    return Single!(NoOp);
  };
  pragmas["pkg-config"] = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, &isStringLiteral))
      throw new Exception("pkg-config packet identifier expected. ");
    auto pkgname = fastcast!(StringExpr) (foldex(ex)).str;
    auto lines = readback("sh -c 'pkg-config --cflags --libs "~pkgname~" 2>&1 || echo pkg-config FAILED'").strip().split("\n");
    if (lines[$-1] == "pkg-config FAILED") {
      throw new Exception("While evaluating pkg-config pragma for "~pkgname~": "~lines[$-2]);
    }
    processCArgs (lines[0].split(" "));
    return Single!(NoOp);
  };
  pragmas["binary"] = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, &isStringLiteral))
      throw new Exception("Binary name expected. ");
    output = (fastcast!(StringExpr) (foldex(ex))).str;
    if (isWindoze()) output ~= ".exe";
    return Single!(NoOp);
  };
  pragmas["linker"] = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, (Expr ex) {
      return !!fastcast!(StringExpr) (foldex(ex));
    }))
      throw new Exception("Linker argument expected. ");
    string str = (fastcast!(StringExpr) (foldex(ex))).str;
    string newarg = "-Wl,"~str;
    // only add once .. becomes relevant in incremental mode
    foreach (arg; extra_linker_args) if (arg == newarg) {
      newarg = null;
      break;
    }
    if (newarg) extra_linker_args = newarg ~ extra_linker_args;
    return Single!(NoOp);
  };
}

static this() {
  New(namespace, { return cast(Namespace) null; });
  New(current_module, { return cast(IModule) null; });
  // placed here because it needs some circular importage
  foldopt ~= delegate Itr(Itr it) {
    auto mae = fastcast!(MemberAccess_Expr) (it);
    if (!mae || mae.stm.name != "ptr") return null;
    
    auto rce = fastcast!(RCE) (mae.base);
    if (!rce) return null;
    if (!(rce.to in isArrayStructType)) return null;
    auto se = fastcast!(StringExpr) (rce.from);
    if (se) return fastcast!(Itr) (se.getPointer());
    auto ar = fastcast!(ArrayMaker) (rce.from);
    if (ar) return fastcast!(Itr) (ar.ptr);
    return null;
  };
}
alias ast.parse.startsWith startsWith;

// from ast.namespace
pragma(set_attribute, C_showsAnySignOfHaving, externally_visible);
extern(C) bool C_showsAnySignOfHaving(Expr ex, string thing) {
  if (fastcast!(MyPlaceholderExpr) (ex)) return false; // nuh-uh.
  auto it = ex.valueType();
  if (Single!(Void) == it) return false;
  if (auto ns = fastcast!(Namespace) (it)) {
    if (ns.lookup(thing)) return true;
  }
  RelNamespace rns;
  if (auto srns = fastcast!(SemiRelNamespace) (it)) rns = srns.resolve();
  if (!rns) rns = fastcast!(RelNamespace) (it);
  if (rns && rns.lookupRel(thing, ex)) return true;
  return false;
}

pragma(set_attribute, _mns_stackframe, externally_visible);
extern(C) Stuple!(IType, string)[] _mns_stackframe(Namespace sup, typeof(Namespace.field) field) {
  Stuple!(IType, string)[] res;
  if (sup) res = sup.get!(ScopeLike).stackframe();
  // variables added to a MiniNamespace are probably taken
  // from elsewhere and are **NOT** part of the stackframe!
  /*foreach (obj; field)
    if (auto var = fastcast!(Variable) (obj._1))
      res ~= stuple(var.type, var.name);*/
  return res;
}

// from ast.fun
static this() {
  // Assumption: SysInt is size_t.
  Expr fpeq(bool neg, Expr ex1, Expr ex2) {
    auto fp1 = fastcast!(FunctionPointer) (ex1.valueType()), fp2 = fastcast!(FunctionPointer) (ex2.valueType());
    if (!fp1 || !fp2) return null;
    return fastalloc!(CondExpr)(fastalloc!(Compare)(reinterpret_cast(Single!(SysInt), ex1), neg, false, true, false, reinterpret_cast(Single!(SysInt), ex2)));
  }
  Expr ptreq(bool neg, Expr ex1, Expr ex2) {
    auto p1 = fastcast!(Pointer) (resolveType(ex1.valueType())), p2 = fastcast!(Pointer) (resolveType(ex2.valueType()));
    if (!p1 || !p2) return null;
    // assert(p1.target == p2.target, Format("Cannot compare ", p1, " and ", p2));
    return fastalloc!(CondExpr)(fastalloc!(Compare)(reinterpret_cast(Single!(SysInt), ex1), neg, false, true, false, reinterpret_cast(Single!(SysInt), ex2)));
  }
  defineOp("==", false /apply/  &fpeq);
  defineOp("==", false /apply/ &ptreq);
  defineOp("!=",  true /apply/  &fpeq);
  defineOp("!=",  true /apply/ &ptreq);
  
  setupPropCall();
}

pragma(set_attribute, rt_print, externally_visible);
extern(C) void rt_print(LLVMFile lf, string s) {
  auto printf = sysmod.lookup("printf");
  buildFunCall(printf, mkString(s~"\n"), "printf").emitLLVM(lf);
}

static this() {
  forcedConversionDg = forcedConversionDg /apply/ delegate Expr(Expr delegate(Expr) prev, Expr ex) {
    if (prev) ex = prev(ex);
    if (auto nono = fastcast!(NoNoDontReturnInMemoryWrapper)(ex.valueType())) {
      return forcedConvert(reinterpret_cast(nono.sup, ex));
    }
    return ex;
  };
  forcedTypeConversionDg = forcedTypeConversionDg /apply/ delegate IType(IType delegate(IType) prev, IType it) {
    if (prev) it = prev(it);
    if (auto nono = fastcast!(NoNoDontReturnInMemoryWrapper)(it))
      return forcedConvert(nono.sup);
    return it;
  };
}

// from ast.math

import ast.modules, ast.prefixfun;
void ast_math_constr() {
  /*foldopt ~= delegate Itr(Itr it) {
    auto fc = fastcast!(FunCall) (it);
    if (!fc) return null;
    bool isFabsMath;
    auto mod = fastcast!(Module) (fc.fun.sup);
    if (fc.fun.name != "fabsf"[] || !fc.fun.extern_c) return null;
    auto arg = foldex(fc.getParams()[0]);
    return fastalloc!(FAbsFExpr)(arg);
  };*/
  Itr substfun(int arity, bool delegate(Function, Module) dg, Expr delegate(Expr[]) dgex, Itr it) {
    auto ftest = it.classinfo is FunCall.classinfo || it.classinfo is PrefixCall.classinfo;
    if (!ftest) return null;
    auto fc = fastcast!(FunCall)(it);
    if (!fc) return null;
    if (fc.getParams().length != arity) return null;
    auto mod = fastcast!(Module)(fc.fun.sup);
    if (!mod) return null;
    if (!dg(fc.fun, mod)) return null;
    
    // auto res = dgex(foldex(fc.getParams()[0]));
    auto pars = fc.getParams();
    foreach (ref par; pars) par = foldex(par);
    auto res = dgex(pars);
    // logln("subst with ", res);
    return res;
  }
  if (!isWindoze()) {
    foldopt ~= &substfun /fix/ stuple(1, (Function fun, Module mod) {
      return fun.name == "fastfloor" && mod is sysmod;
    }, delegate Expr(Expr[] args) {
      return fastalloc!(FPAsInt)(lookupOp("+",
        fastalloc!(IntrinsicExpr)("llvm.floor.f32"[], args, Single!(Float)),
        fastalloc!(FloatExpr)(0.25)));
    });
  }
  foldopt ~= &substfun /fix/ stuple(2, (Function fun, Module mod) {
    return (fun.name == "copysignf" || fun.name == "[wrap]copysignf") && fun.extern_c;
  }, delegate Expr(Expr[] args) {
    auto Int = Single!(SysInt), Float = Single!(Float);
    return reinterpret_cast(Float, lookupOp("|",
      lookupOp("&", reinterpret_cast(Int, args[0]), mkInt(0x7fff_ffff)),
      lookupOp("&", reinterpret_cast(Int, args[1]), mkInt(0x8000_0000))
    ));
  });
  void addCIntrin(int arity, string funname, IType ret, string intrin) {
    foldopt ~= &substfun /fix/ stuple(arity, stuple(funname) /apply/ (string funname, Function fun, Module mod) {
      return (fun.name == funname || fun.name == qformat("[wrap]", funname)) && fun.extern_c;
    }, stuple(intrin, ret) /apply/ delegate Expr(string intrin, IType ret, Expr[] args) {
      foreach (ref arg; args) {
        if (!gotImplicitCast(arg, ret, (IType it) { return test(ret == it); }))
          throw new Exception("invalid argument for intrinsic");
      }
      return fastalloc!(IntrinsicExpr)(intrin, args, ret);
    });
  }
  addCIntrin(1, "sqrtf" , Single!(Float), "llvm.sqrt.f32");
  // do in software, intrinsic is slow
  // addCIntrin(1, "sinf"  , Single!(Float), "llvm.sin.f32");
  // addCIntrin(1, "cosf"  , Single!(Float), "llvm.cos.f32");
  if (!isWindoze()) {
    addCIntrin(1, "floorf", Single!(Float), "llvm.floor.f32");
  }
  addCIntrin(1, "fabsf" , Single!(Float), "llvm.fabs.f32");
  addCIntrin(1, "exp"   , Single!(Float), "llvm.exp.f32");
  addCIntrin(1, "log"   , Single!(Float), "llvm.log.f32");
  addCIntrin(2, "powf"  , Single!(Float), "llvm.pow.f32");
  
  bool isInt(IType it) { return test(Single!(SysInt) == it); }
  bool isFloat(IType it) { return test(Single!(Float) == it); }
  bool isDouble(IType it) { return test(Single!(Double) == it); }
  bool isLong(IType it) { return test(Single!(Long) == it); }
  bool isPointer(IType it) { return test(fastcast!(Pointer)~ it); }
  bool isBool(IType it) { if (!sysmod) return false; return test(it == fastcast!(IType)(sysmod.lookup("bool"))); }
  Expr handleIntMath(string op, Expr ex1, Expr ex2) {
    bool b1 = isBool(ex1.valueType()), b2 = isBool(ex2.valueType());
    if (!gotImplicitCast(ex1, Single!(SysInt), &isInt) || !gotImplicitCast(ex2, Single!(SysInt), &isInt))
      return null;
    Expr res;
    bool ntcache, ntcached;
    bool nontrivial() {
      if (ntcached) return ntcache;
      auto ie1 = fastcast!(IntExpr) (foldex(ex1));
      if (!ie1) { ntcache = ntcached = true; return true; }
      auto ie2 = fastcast!(IntExpr) (foldex(ex2));
      if (!ie2) { ntcache = ntcached = true; return true; }
      ntcached = true; ntcache = false; return false;
    }
    if (!res) res = fastalloc!(AsmIntBinopExpr)(ex1, ex2, op);
    /*if (qformat(res).find("+ 0) + 0) + 0) + 0) + 0) + 0) + 0)") != -1) {
      logln("?? ", res);
      fail;
    }*/
    if (b1 && b2) res = reinterpret_cast(fastcast!(IType) (sysmod.lookup("bool")), res);
    return res;
  }
  Expr handleIntUnary(string op, Expr ex) {
    if (!gotImplicitCast(ex, Single!(SysInt), &isInt))
      return null;
    return fastalloc!(AsmIntUnaryExpr)(ex, op);
  }
  Expr handleLongUnary(string op, Expr ex) {
    if (!gotImplicitCast(ex, Single!(Long), &isLong))
      return null;
    return fastalloc!(AsmLongUnaryExpr)(ex, op);
  }
  Expr handleNeg(Expr ex) {
    return lookupOp("-", mkInt(0), ex);
  }
  Expr handlePointerMath(string op, Expr ex1, Expr ex2) {
    Pointer e1pt;
    if (auto p = fastcast!(Pointer) (resolveTup(ex2.valueType()))) {
      if (op == "-") {
        // return null; // wut
        // pointer - pointer is defined! (if they have the same types)
        auto p2 = fastcast!(Pointer)(resolveTup(ex1.valueType()));
        if (p != p2) return null;
      } else {
        swap(ex1, ex2);
        e1pt = p;
      }
    }
    if (!e1pt) e1pt = fastcast!(Pointer) (resolveTup(ex1.valueType()));
    if (!e1pt) return null;
    auto e2pt = fastcast!(Pointer) (resolveTup(ex2.valueType()));
    if (e2pt) {
      return handleIntMath("/",
        handleIntMath("-",
          reinterpret_cast(Single!(SysInt), ex1),
          reinterpret_cast(Single!(SysInt), ex2)
        ),
        llvmval(e1pt.target.llvmSize())
      );
    }
    if (fastcast!(Float) (ex2.valueType())) {
      logln(ex1, " ", op, " ", ex2, "; WTF?! ");
      logln("is ", ex1.valueType(), " and ", ex2.valueType());
      // fail();
      throw new Exception("Invalid pointer op");
    }
    if (auto ie = fastcast!(IntExpr) (ex2)) { // shortcut
      ex2 = llvmval(llmul(qformat(ie.num), e1pt.target.llvmSize()));
    } else {
      ex2 = handleIntMath("*", ex2, llvmval(e1pt.target.llvmSize()));
    }
    if (!ex2) return null;
    return reinterpret_cast(ex1.valueType(), handleIntMath(op, reinterpret_cast(Single!(SysInt), ex1), ex2));
  }
  Expr handleFloatMath(string op, Expr ex1, Expr ex2) {
    if (Single!(Double) == ex1.valueType()) {
      ex1 = foldex(ex1);
      if (!fastcast!(DoubleExpr) (ex1))
        return null;
    }
    
    if (Single!(Double) == ex2.valueType()) {
      ex2 = foldex(ex2);
      if (!fastcast!(DoubleExpr) (ex2))
        return null;
    }
    
    if (fastcast!(DoubleExpr) (ex1) && fastcast!(DoubleExpr) (ex2)) return null;
    
    if (!gotImplicitCast(ex1, Single!(Float), &isFloat) || !gotImplicitCast(ex2, Single!(Float), &isFloat))
      return null;
    
    return fastalloc!(AsmFloatBinopExpr)(ex1, ex2, op);
  }
  Expr handleDoubleMath(string op, Expr ex1, Expr ex2) {
    if (Single!(Double) != resolveTup(ex1.valueType())
     && Single!(Double) != resolveTup(ex2.valueType()))
      return null;
    if (!gotImplicitCast(ex1, Single!(Double), &isDouble) || !gotImplicitCast(ex2, Single!(Double), &isDouble))
      return null;
    
    return fastalloc!(AsmDoubleBinopExpr)(ex1, ex2, op);
  }
  Expr handleLongMath(string op, Expr ex1, Expr ex2) {
    if (Single!(Long) != resolveTup(ex1.valueType())
     && Single!(Long) != resolveTup(ex2.valueType()))
      return null;
    if (!gotImplicitCast(ex1, Single!(Long), &isLong) || !gotImplicitCast(ex2, Single!(Long), &isLong))
      return null;
    
    return mkLongExpr(ex1, ex2, op);
  }
  void defineOps(Expr delegate(string op, Expr, Expr) dg, bool reduced = false) {
    string[] ops;
    if (reduced) ops = ["+", "-"]; // pointer math
    else ops = ["+", "-", "&", "|", "*", "/", "%", "<<", ">>", ">>>", "xor"];
    foreach (op; ops)
      defineOp(op, op /apply/ dg);
  }
  defineOp("¬", "¬" /apply/ &handleIntUnary);
  defineOp("¬", "¬" /apply/ &handleLongUnary);
  defineOp("-", &handleNeg);
  defineOps(&handleIntMath);
  defineOps(&handleFloatMath);
  defineOps(&handleDoubleMath);
  defineOps(&handleLongMath);
  defineOps(&handlePointerMath, true);
}

pragma(set_attribute, printThing, externally_visible);
extern(C) void printThing(LLVMFile lf, string s, Expr ex) {
  (buildFunCall(sysmod.lookup("printf"), mkTupleExpr(mkString(s), ex), "mew")).emitLLVM(lf);
}

// from ast.fun
import ast.casting;
Object gotFunRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  Object obj;
  if (!rest(text, "tree.expr _tree.expr.arith"[], &obj)) return null;
  if (auto fun = fastcast!(Function) (obj)) {
    return fastalloc!(FunRefExpr)(fun);
  }
  if (auto os = fastcast!(OverloadSet) (obj)) {
    Function matched;
    foreach (fun; os.funs) {
      if (fastcast!(PrefixFunction) (fun)) continue;
      if (matched) { text.setError("Cannot take address of overload set"); return null; }
      matched = fun;
    }
    if (matched) return fastalloc!(FunRefExpr)(matched);
  }
  return null;
}
mixin DefaultParser!(gotFunRefExpr, "tree.expr.fun_ref"[], "2101"[], "&"[]);

Object gotAsType(ref string text, ParseCb cont, ParseCb rest) {
  string ident;
  auto t2 = text;
  if (t2.accept("(") && t2.gotIdentifier(ident) && t2.accept(")")) {
    text = t2;
  } else {
    if (!text.gotIdentifier(ident)) text.failparse("Identifier expected for as_type");
  }
  auto ta = fastalloc!(TypeAlias)(cast(IType) null, ident, false);
  {
    auto as_type_ns = fastalloc!(MiniNamespace)("as_type_ident_override");
    as_type_ns.sup = namespace();
    as_type_ns.internalMode = true;
    as_type_ns.add(ta);
    namespace.set(as_type_ns);
    scope(exit) namespace.set(as_type_ns.sup);
    if (!rest(text, "type", &ta.base))
      text.failparse("Type expected");
  }
  return ta;
}
mixin DefaultParser!(gotAsType, "type.as_type", "8", "as_type");

// from ast.casting
import llvmfile, ast.vardecl;
alias ast.types.typeToLLVM typeToLLVM;
pragma(set_attribute, _reinterpret_cast_expr, externally_visible);
extern(C) void _reinterpret_cast_expr(RCE rce, LLVMFile lf) {
  auto from = typeToLLVM(rce.from.valueType()), to = typeToLLVM(rce.to);
  string v = save(lf, rce.from);
  // logln("rce ", rce, " (", rce.from.valueType(), ", ", rce.to, "): ", from, " -> ", to);
  llcast(lf, from, to, v, rce.from.valueType().llvmSize());
}
pragma(set_attribute, llcast, externally_visible);
extern(C) void llcast(LLVMFile lf, string from, string to, string v, string fromsize = null) {
  if (from != to) {
    checkcasttypes(from, to);
    if (from.endsWith("}") || from.endsWith("]") || from.endsWith(">") || to.endsWith("}") || to.endsWith("]")) {
      if ((from.endsWith("}") || from.endsWith(">"))&& (to.endsWith("}") || to.endsWith(">"))) {
        bool fromIsStruct = !!from.endsWith("}"), toIsStruct = !!to.endsWith("}");
        string[] a, b;
        if (fromIsStruct) llvmtype.structDecompose(from, (string s) { a ~= s; });
        else a = getVecTypes(from);
        if (  toIsStruct) llvmtype.structDecompose(  to, (string s) { b ~= s; });
        else b = getVecTypes(  to);
        if (a.length == b.length) {
          bool samelayout = true;
          foreach (i, t1; a) {
            auto t2 = b[i];
            // if types are not (the same or both pointers)
            if (!(t1 == t2 || t1.endsWith("*") && t2.endsWith("*"))) {
              samelayout = false;
              break;
            }
          }
          if (samelayout) {
            // logln("use elaborate conversion for ", from, " -> ", to);
            // extract, cast and recombine
            string res = "undef";
            foreach (i, t1; a) {
              auto t2 = b[i];
              string val;
              if (fromIsStruct) val = save(lf, "extractvalue ", from, " ", v, ", ", i);
              else val = save(lf, "extractelement ", from, " ", v, ", i32 ", i);
              if (t1 != t2) {
                llcast(lf, t1, t2, val);
                val = lf.pop();
              }
              if (toIsStruct) res = save(lf, "insertvalue ", to, " ", res, ", ", t2, " ", val, ", ", i);
              else res = save(lf, "insertelement ", to, " ", res, ", ", t2, " ", val, ", i32 ", i);
            }
            lf.push(res);
            return;
          }
        }
      }
      if (llvmTypeIs16Aligned(from)) {
        auto ap = alloca(lf, "1", from);
        auto fs = bitcastptr(lf, from, to, ap);
        put(lf, "store ", from, " ", v, ", ", from, "* ", ap);
        v = save(lf, "load ", to, "* ", fs);
      } else {
        auto ap = alloca(lf, "1", to);
        auto fs = bitcastptr(lf, to, from, ap);
        put(lf, "store ", from, " ", v, ", ", from, "* ", fs);
        v = save(lf, "load ", to, "* ", ap);
      }
    } else if (from.endsWith("*") && to == "i32") {
      v = save(lf, "ptrtoint ", from, " ", v, " to i32");
    } else if (from == "i32" && to.endsWith("*")) {
      v = save(lf, "inttoptr i32 ", v, " to ", to);
    } else {
      v = save(lf, "bitcast ", from, " ", v, " to ", to);
    }
  }
  push(lf, v);
}

pragma(set_attribute, _exactly_equals, externally_visible);
extern(C) bool _exactly_equals(IType a, IType b) {
  auto pa = fastcast!(Pointer)~ a, pb = fastcast!(Pointer)~ b;
  if (pa && pb) return _exactly_equals(pa.target, pb.target);
  if (!pa && pb || pa && !pb) return false;
  IType resolveMyType(IType it) {
    if (fastcast!(TypeAlias) (it)) return it;
    if (auto tp = it.proxyType())
      return resolveMyType(tp);
    return it;
  }   
  auto
    ca = fastcast!(TypeAlias) (resolveMyType(a)),
    cb = fastcast!(TypeAlias) (resolveMyType(b));
  if (!ca && !cb) return test(a == b);
  if ( ca && !cb) return false;
  if (!ca &&  cb) return false;
  if ( ca &&  cb) return (ca.name == cb.name) && ca.base == cb.base;
}

// from ast.arrays
static this() {
  defineOp("=="[], delegate Expr(Expr ex1, Expr ex2) {
    bool isArray(IType it) { return !!fastcast!(Array) (it); }
    auto oex1 = ex1, oex2 = ex2;
    if (!gotImplicitCast(ex1, &isArray) || !gotImplicitCast(ex2, &isArray))
      return null;
    auto a1 = fastcast!(Array) (ex1.valueType());
    {
      bool cres;
      if (constantStringsCompare(oex1, oex2, &cres)) return cres?True:False;
    }
    return tmpize_maybe(ex1, delegate Expr(Expr ex1) {
      return tmpize_maybe(ex2, delegate Expr(Expr ex2) {
        auto e1l = getArrayLength(ex1), e2l = getArrayLength(ex2),
              e1p = reinterpret_cast(voidp, getArrayPtr(ex1)), e2p = reinterpret_cast(voidp, getArrayPtr(ex2)),
              mcl = lookupOp("*", e1l, llvmval(a1.elemType.llvmSize()));
        return fastalloc!(CondExpr)(fastalloc!(AndOp)(
          fastalloc!(Compare)(e1l, "==", e2l),
          fastalloc!(Compare)(mkInt(0), "==", buildFunCall(
            sysmod.lookup("memcmp"),
            mkTupleExpr(e1p, e2p, mcl),
            "memcmp for array equal"
          )
        )));
        // return iparse!(Expr, "array_eq"[], "tree.expr.eval.cond"[])
        //               (`eval (e1l == e2l && memcmp(e1p, e2p, mcl) == 0)`,
        //                "e1l", e1l, "e2l", e2l, "e1p", e1p, "e2p", e2p, "mcl", mcl);
      });
    });
  });
}

// from ast.scopes
Object gotScope(ref string text, ParseCb cont, ParseCb rest) {
  // Copypasted from ast.structure
  auto rtptbackup = RefToParentType();
  scope(exit) RefToParentType.set(rtptbackup);
  RefToParentType.set(Single!(Pointer, Single!(Void))); // ast.newexpr depends on this!
  
  auto rtpmbackup = *RefToParentModify();
  scope(exit) *RefToParentModify.ptr() = rtpmbackup;
  *RefToParentModify.ptr() = delegate Expr(Expr baseref) { return baseref; };
  // end copypaste
  
  if (auto res = rest(text, "tree.stmt.aggregate")) return res; // always scope anyway
  auto sc = fastalloc!(Scope)();
  sc.configPosition(text);
  
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  auto t2 = text;
  Statement _body;
  if (rest(t2, "tree.stmt", &_body)) { text = t2; sc.addStatement(_body); return sc; }
  t2.failparse("Couldn't match scope");
}
mixin DefaultParser!(gotScope, "tree.scope");


pragma(set_attribute, _line_numbered_statement_emitLLVM, externally_visible);
extern(C)
void _line_numbered_statement_emitLLVM(LineNumberedStatement lns, LLVMFile lf) {
  if (!lf.debugmode || releaseMode) return;
  auto frameinfo = fastcast!(LValue)(namespace().lookup("__frameinfo", true));
  auto fname = namespace().get!(Function).name;
  if (frameinfo) {
    auto lr = fastcast!(RelNamespace)(frameinfo.valueType());
    if (!lr) {
      logln("no relnamespace: ", frameinfo);
      fail; 
    }
    auto pos = fastcast!(LValue)(lr.lookupRel("pos", frameinfo));
    if (!pos) {
      logln("no pos in: ", lr);
      fail;
    }
    string name; int line;
    lns.getInfo(name, line);
    if (!name || name.startsWith("<internal")) return;
    /*if (fname == "raise") {
      logln("emit line number assignment at ", lns, " ", frameinfo, " in ", namespace());
      logln("@", name, ":", line);
    }*/
    if (name.find("/std/") != -1) name = "std/"~name.between("/std/", "");
    emitAssign(lf, pos, mkString(qformat(name, ":", line)));
  } /*else if (fname == "raise") {
    logln("bad bad no frameinfo");
    fail;
  }*/
  return;
}

pragma(set_attribute, _is_cheap, externally_visible);
extern(C) bool _is_cheap(Expr ex, CheapMode mode) {
  bool cheaprecurse(Expr ex) {
    // Not sure if valid, but needed for prefix(foo_).(bar) .. maybe add a flag for that case
    if (auto pt = fastcast!(PlaceholderToken) (ex))
      return true;
    if (auto rc = fastcast!(RC) (ex))
      return cheaprecurse (rc.from);
    if (fastcast!(Variable) (ex))
      return true;
    if (auto mae = fastcast!(MemberAccess_Expr) (ex))
      return cheaprecurse (mae.base);
    if (fastcast!(Literal) (ex))
      return true;
    if (fastcast!(StringExpr) (ex))
      return true;
    if (auto ea = fastcast!(ExprAlias) (ex))
      return cheaprecurse(ea.base);
    if (fastcast!(GlobVar) (ex))
      return true;
    if (fastcast!(LLVMValue) (ex))
      return true;
    if (auto re = fastcast!(RefExpr) (ex))
      return cheaprecurse (re.src);
    if (auto de = fastcast!(DerefExpr) (ex))
      return cheaprecurse (de.src);
    if (auto lvamv = fastcast!(LValueAsMValue) (ex))
      return cheaprecurse (lvamv.sup);
    if (auto na = fastcast!(NamedArg) (ex))
      return cheaprecurse (na.base);
    
    if (mode == CheapMode.Flatten) {
      if (auto sl = fastcast!(StructLiteral) (ex)) return true;
      if (auto rt = fastcast!(RefTuple) (ex)) return true;
      if (auto mae = fastcast!(MemberAccess_Expr) (ex))
        return cheaprecurse (mae.base);
    } else { // CheapMode.Multiple
      if (auto sl = fastcast!(StructLiteral) (ex)) {
        foreach (ex2; sl.exprs) if (!cheaprecurse(ex2)) return false;
        return true;
      }
      if (auto rt = fastcast!(RefTuple) (ex)) {
        foreach (ex2; rt.getAsExprs()) if (!cheaprecurse(ex2)) return false;
        return true;
      }
    }
    // logln("cheap? ", (cast(Object) (ex)).classinfo.name, " ", ex);
    return false;
  }
  return cheaprecurse(ex);
}

// from ast.vardecl
pragma(set_attribute, _tmpize_maybe, externally_visible);
extern(C) Expr _tmpize_maybe(Expr thing, E2ERdg dg, bool force) {
  if (auto ea = fastcast!(ExprAlias) (thing)) thing = ea.base;
  if (!force) {
    bool cheap(Expr ex) {
      return _is_cheap(ex, CheapMode.Multiple);
    }
    if (cheap(thing))
      return dg(thing, null); // cheap to emit
  }
  auto wurble = fastalloc!(WithTempExpr)(thing, dg);
  if (!wurble.isValid()) return null;
  return wurble;
}


string renderProgbar(int total, int current) {
  auto progbar = new char[total];
  for (int i = 0; i < total; ++i) {
    if (i < current) progbar[i] = '=';
    else if (i == current) progbar[i] = '>';
    else progbar[i] = ' ';
  }
  return Format("[", progbar, "] ", (current*100)/total, "%");
}

extern(C) {
  int open(char* filename, int flags, size_t mode);
  int close(int fd);
  const O_CREAT = 0100, O_EXCL = 0200;
}

string error;

import tools.mersenne;
string tmpnam(string base, string ext) {
  while (true) {
    auto name = Format(base, rand(), ext), namep = toStringz(name);
    auto fd = open(namep, O_CREAT | O_EXCL, 0600);
    if (fd != -1) {
      close(fd);
      return name;
    }
  }
}

import ast.parse;

import ast.modules;

import ast.fun, ast.namespace, ast.variable, ast.base, ast.scopes;

extern(C) void exit(int);

import tools.time, quicksort;
import ast.fold;

int[int] sizesums;

void gatherSizeStats(Module mod) {
  int[void*] ns_sizes;
  void recurse(ref Iterable it) {
    if (auto ns = fastcast!(Namespace) (it)) {
      ns_sizes[cast(void*) ns] = ns.max_field_size;
    }
    it.iterate(&recurse);
  }
  mod.iterate(&recurse);
  synchronized foreach (value; ns_sizes.values) sizesums[value] ++;
  logSmart!(false)(mod.name, ": namespace field size distribution");
  int maxsz;
  foreach (entry; sizesums.values) if (entry > maxsz) maxsz = entry;
  const Width = 40;
  foreach (entry; sizesums.keys.dup.sort) {
    auto sz = sizesums[entry];
    auto frac = sz * 1f / maxsz;
    string octs;
    for (int i = 0; i < cast(int) (frac*Width); ++i) octs ~= "#";
    logSmart!(false)(entry, ": ", sz, "\t", octs);
  }
}

void postprocessModule(Module mod, LLVMFile lf) {
  void recurse(ref Iterable it) {
    if (auto fc = fastcast!(FunCall) (it)) {
      if (fc.fun.weak) {
        auto ti = fc.fun.get!(TemplateInstance);
        if (ti) {
          ti.emitCopy(true); // called funs must be emitted in every
                             // module that _uses_ them, because on
                             // win32, weak symbols are always local.
        }
      }
    }
    if (auto dep = fastcast!(Dependency) (it)) {
      dep.emitDependency(lf);
    }
    it.iterate(&recurse);
  }
  // TODO check if necessary
  // if (isWindoze()) mod.iterate(&recurse);
  // result: mostly below 7
  // gatherSizeStats(mod);
}

bool ematSysmod;

bool delegate(Module) dontReemit;

bool initedSysmod;
void lazySysmod() {
  if (initedSysmod) return;
  initedSysmod = true;
  setupSysmods();
}

bool allowProgbar = true;

struct CompileSettings {
  bool saveTemps, optimize, preopt, debugMode, profileMode, singlethread;
}

// structural verifier
void verify(Iterable it) {
  int[] res;
  void handle(ref Iterable it) {
    auto outside = res; res = null;
    int[][] list;
    Iterable[] subs;
    void handle2(ref Iterable it) {
      if (auto sae = fastcast!(StatementAndExpr) (it))
        res ~= sae.marker;
      subs ~= it;
      handle(it);
      list ~= res;
      res = null;
    }
    it.iterate(&handle2, IterMode.Lexical);
    res = outside;
    foreach (i1, ar1; list) foreach (i2, ar2; list) if (i2 != i1) {
      foreach (e1; ar1) foreach (e2; ar2) if (e1 == e2) {
        logln("Error: sae marker collision (", ar1, ", ", ar2, ") beneath ", fastcast!(Object) (it).classinfo.name, "{1}", subs[i1], " {2}", subs[i2]);
        fail;
      }
    }
    foreach (ar; list) res ~= ar;
  }
  handle(it);
  logln(res.length, " markers checked, no collisions. ");
}

string get_llc_cmd(bool optimize, bool saveTemps, ref string fullcommand) {
  string cpu = "core2";
  if (isARM) cpu = null;
  
  string cpumode;
  if (cpu) cpumode = "-mcpu="~cpu~" ";
  
  string llc_optflags;
  if (optimize) {
    void optrun(string flags, string marker = null) {
      if (marker) marker ~= ".";
      string optfile = ".obj/"~output~".opt."~marker~"bc";
      fullcommand ~= " |opt "~flags~"-lint -";
      if (saveTemps) fullcommand ~= " |tee "~optfile;
    }
    string fpmathopts = "-enable-fp-mad -enable-no-infs-fp-math -enable-no-nans-fp-math -enable-unsafe-fp-math -fp-contract=fast "/*-vectorize */"-vectorize-loops -tailcallopt ";
    string optflags = "-internalize-public-api-list=main"~preserve~" -O3 "~fpmathopts;
    string passflags = "-std-compile-opts ";
    if (!isWindoze()) passflags ~= "-internalize -std-link-opts "; // don't work under win32 (LLVMMMM :shakes fist:)
    optrun(cpumode~passflags~optflags);
    llc_optflags = optflags;
  }
  return cpumode~llc_optflags;
}

extern(C) int mkdir(char*, int);
string delegate() compile(string file, CompileSettings cs, bool force = false) {
  scope(failure)
    logSmart!(false)("While compiling ", file);
  while (file.startsWith("./")) file = file[2 .. $];
  auto lf = fastalloc!(LLVMFile)(cs.optimize, cs.debugMode, cs.profileMode, file);
  lazySysmod();
  string srcname, objname;
  if (auto end = file.endsWith(EXT)) {
    srcname = ".obj/" ~ end ~ ".ll";
    if (isWindoze || cs.optimize)
      objname = ".obj/" ~ end ~ ".bc";
    else
      objname = ".obj/" ~ end ~ ".o";
    auto path = srcname[0 .. srcname.rfind("/")];
    string mew = ".";
    foreach (component; path.split("/")) {
      mew = mew.qsub(component);
      mkdir(toStringz(mew), 0755);
    }
  } else assert(false);
  scope(exit) {
    if (!cs.saveTemps)
      unlink(srcname.toStringz());
  }
  auto modname = file.replace("/", ".")[0..$-3];
  auto start_parse = sec();
  bool fresh = true;
  auto mod = lookupMod(modname);
  if (!mod) throw new Exception(Format("No such module: ", modname));
  if (mod.dontEmit) return null;
  if (mod.alreadyEmat || !force && dontReemit && dontReemit(mod)) {
    // mod.doneEmitting = true;
    return objname /apply/ (string objname) { return objname; }; // fresh
  }
  fixupMain();
  auto len_parse = sec() - start_parse;
  double len_opt;
  len_opt = time({
    .postprocessModule(mod, lf);
  }) / 1_000_000f;
  // verify(mod);
  auto len_gen = time({
    mod.emitLLVM(lf);
  }) / 1_000_000f;
  // logSmart!(false)(len_parse, " to parse, ", len_opt, " to optimize. ");
  Stuple!(string, float)[] entries;
  foreach (key, value; ast.namespace.bench) entries ~= stuple(key, value);
  entries.qsort(ex!("a, b -> a._1 > b._1"));
  float total = 0;
  foreach (entry; entries) total += entry._1;
  // logSmart!(false)("Subsegments: ", entries, "; total ", total);
  mod.alreadyEmat = true;
  return stuple(len_parse, len_gen, objname, srcname, lf, mod, cs) /apply/
  (double len_parse, double len_gen, string objname, string srcname, LLVMFile lf, Module mod, CompileSettings cs) {
    scope(exit)
      if (!cs.saveTemps)
        unlink(srcname.toStringz());
    scope f = fastalloc!(BufferedFile)(srcname, FileMode.OutNew);
    scope(exit) delete f.buffer; // yuck
    auto len_emit = time({
      lf.dumpLLVM((string s) { f.write(cast(ubyte[]) s); });
      lf.free;
    }) / 1_000_000f;
    f.close;
    string flags;
    if (false && cs.preopt) flags = "-O3 -lint ";
    // if (platform_prefix.startsWith("arm-")) flags = "-meabi=5";
    // auto cmdline = Format(my_prefix(), "as ", flags, " -o ", objname, " ", srcname, " 2>&1");
    string cmdline;
    if (cs.preopt && !cs.optimize) {
      cmdline = Format("opt ", flags);
    } else {
      cmdline = Format("llvm-as ", flags);
    }
    if (isWindoze || cs.optimize) {
      cmdline ~= Format("-o ", objname, " ", srcname, " 2>&1");
    } else {
      string bogus;
      cmdline ~= Format("-o - ", srcname, " |opt -march=x86 - "~get_llc_cmd(cs.optimize, cs.saveTemps, bogus)~" |llc -march=x86 - -filetype=obj -o ", objname);
    }
    
    logSmart!(false)("> (", len_parse, "s,", len_gen, "s,", len_emit, "s) ", cmdline);
    if (auto res = system(cmdline.toStringz())) {
      logln("ERROR: Compilation failed with ", res, " ", getErrno());
      exit(res);
    }
    return objname;
  };
}

T takeFromEnd(T)(ref T[] array) {
  if (!array.length) fail;
  auto res = array[$-1];
  array = array[0..$-1];
  return res;
}

void genCompilesWithDepends(string file, CompileSettings cs, void delegate(string delegate()) assemble) {
  while (file.startsWith("./")) file = file[2 .. $];
  auto modname = file.replace("/", ".")[0..$-3];
  bool[string] done;
  Module[] todo;
  lazySysmod();
  setupStaticBoolLits();
  auto start = lookupMod(modname);
  done[start.name] = true; // mark here to unbreak circular import of main file (really only relevant for testsuite)
  
  todo ~= start.getAllModuleImports();
  while (todo.length) {
    auto cur = todo.takeFromEnd();
    if (cur.name in done) continue;
    if (auto nuMod = compile(cur.name.replace(".", "/") ~ EXT, cs))
      assemble(nuMod);
    done[cur.name] = true;
    todo ~= cur.getAllModuleImports();
  }
  
  finalizeSysmod(start);
  auto firstObj = compile(file, cs, true);
  assemble(firstObj);
}

string[] compileWithDepends(string file, CompileSettings cs) {
  string[] objs;
  int waits;
  auto seph = new Semaphore;
  void process(string delegate() dg) {
    if (cs.singlethread && false) objs ~= dg();
    else {
      synchronized {
        waits++;
        if (!emitpool) emitpool = fastalloc!(Threadpool)(4);
      }
      emitpool.addTask(stuple(dg, seph, &objs) /apply/ (string delegate() dg, Semaphore seph, string[]* objs) {
        auto obj = dg();
        synchronized {
          *objs ~= obj;
          seph.release();
        }
      });
    }
  }
  void waitup() {
    if (waits) {
      for (int i = 0; i < waits; ++i)
        seph.acquire();
    }
  }
  scope(failure) waitup;
  file.genCompilesWithDepends(cs, &process);
  waitup;
  return objs;
}

void dumpXML() {
  void callback(ref Iterable it) {
    if (fastcast!(NoOp) (it)) return;
    string info = Format("<node classname=\"", (fastcast!(Object)~ it).classinfo.name, "\"");
    if (auto n = fastcast!(Named)~ it)
      info ~= Format(" name=\"", n.getIdentifier(), "\"");
    if (auto i = cast(HasInfo) it)
      info ~= Format( " info=\"", i.getInfo(), "\"");
    info ~= " >";
    logln(info); 
    it.iterate(&callback);
    logln("</node>");
  }
  foreach (mod; fastcast!(Module) (sysmod)~modlist) {
    logln("----module ", mod.name);
    mod.iterate(&callback);
    logln("----done"); 
  }
  std.c.stdio.fflush(stdout);
}

void link(string[] objects, bool optimize, bool saveTemps = false) {
  if (dumpXMLRep) dumpXML();
  scope(success)
    if (!saveTemps)
      foreach (obj; objects)
        unlink(obj.toStringz());
  // string linkedfile = ".obj/"~output~".all.bc";
  string linkedfile;
  if (isWindoze || optimize) linkedfile = ".obj/"~output~".all.bc";
  else linkedfile = ".obj/"~output~".all.o";
  
  string objfile, objlist;
  foreach (obj; objects) objlist ~= obj ~ " ";
  if (!isWindoze && !optimize) {
    objfile = objlist;
  } else {
    string fullcommand = "llvm-link "~objlist;
    
    fullcommand ~= " |llvm-dis - |sed -e s/^define\\ weak_odr\\ /define\\ /g -e s/=\\ weak_odr\\ /=\\ /g |llvm-as";
    if (saveTemps) fullcommand ~= " |tee "~linkedfile;
    
    objfile = ".obj/"~output~".o";
    // -mattr=-avx,-sse41 
    fullcommand ~= " |llc - "~get_llc_cmd(optimize, saveTemps, fullcommand)~"-filetype=obj -o "~objfile;
    logSmart!(false)("> ", fullcommand);
    if (system(fullcommand.toStringz()))
      throw new Exception("link failed");
  }
  
  string locallibfolder;
  if (platform_prefix) {
    locallibfolder = qformat("-L/usr/", platform_prefix[0..$-1], "/lib/ ");
  }
  string mode;
  if (!isARM()) mode = "-m32 ";
  string linkflags = mode~"-Wl,--gc-sections "~locallibfolder~"-L/usr/local/lib";
  string cmdline = my_prefix()~"gcc "~linkflags~" -o "~output~" "~objfile~" ";
  foreach (larg; linkerArgs ~ extra_linker_args) cmdline ~= larg ~ " ";
  logSmart!(false)("> ", cmdline);
  if (system(cmdline.toStringz()))
    throw new Exception("Failed to link");
}

import tools.threadpool;
Threadpool emitpool;

version(Windows) {
} else {
  import std.c.unix.unix: sigset_t, sigemptyset, SIGXCPU;
  extern(C) {
    int sigaddset(sigset_t*, int);
    int sigprocmask(int, sigset_t*, sigset_t*);
    int sigwait(sigset_t*, int*);
    const SIG_BLOCK = 0;
  }
}

alias ast.modules.exists exists;

void incbuild(string start,
          CompileSettings cs, bool runMe)
{
  string undo(string mod) {
    return mod.replace(".", "/") ~ EXT;
  }
  void translate(string file, ref string obj, ref string asmf) {
    if (auto pre = file.endsWith(EXT)) {
      asmf = ".obj/" ~ pre ~ ".ll";
      if (isWindoze() || cs.optimize)
        obj  = ".obj/" ~ pre ~ ".bc";
      else
        obj = ".obj/" ~ pre ~ ".o";
    } else assert(false);
  }
  bool[string] checking;
  bool[string] neededRebuild; // prevent issue where we rebuild a mod, after which
                              // it obviously needs no further rebuild, preventing
                              // another module from realizing that it needs to be rebuilt also
  bool needsRebuild(Module mod) {
    if (mod.dontEmit) return false;
    
    auto file = mod.name.undo();
    string obj, asmf;
    file.translate(obj, asmf);
    file = findfile(file);
    
    auto start2 = findfile(start);
    if (file == start2) return false; // this gets emitted last! don't reparse regardless
    if (!obj.exists()) { neededRebuild[mod.sourcefile] = true; return true; }
    
    // if (mod.name != "sys")
    //   logln("needsRebuild? ", file, " ", start2, " ", mod.dontEmit, " ", mod is sysmod, " ", isUpToDate(file, obj), " ", !!(mod.name in checking), " ", mod.getAllModuleImports());
    
    if (mod is sysmod || !isUpToDate(file, obj)) { neededRebuild[mod.sourcefile] = true; return true; }
    if (mod.name in checking) return false; // break the circle
    checking[mod.name] = true;
    scope(exit) checking.remove(mod.name);
    foreach (mod2; mod.getAllModuleImports())
      if (mod2 !is sysmod && (mod2.sourcefile in neededRebuild || needsRebuild(mod2))) {
        // logln("need to rebuild ", mod.name, " because of ", mod2.name, ", which it depends on");
        neededRebuild[mod.sourcefile] = true;
        return true;
      }
    return false;
  }
  dontReemit = delegate bool(Module mod) {
    return !needsRebuild(mod);
  };
  lazySysmod();
  try {
    string[] objs = start.compileWithDepends(cs);
    objs.link(cs.optimize, true);
  } catch (Exception ex) {
    logSmart!(false) (ex);
    return;
  }
  if (runMe) {
    auto cmd = "./"~output;
    version(Windows) cmd = output;
    logSmart!(false)("> ", cmd); system(toStringz(cmd));
  }
}

version(Windows) { const string pathsep = "\\"; }
else { const string pathsep = "/"; }

version(Windows) {
  extern(Windows) int GetModuleFileNameA(void*, char*, int);
  string myRealpath(string path) {
    char[1024] mew;
    auto res = GetModuleFileNameA(null, /*toStringz(path)*/ mew.ptr, mew.length);
    if (!res) throw new Exception("GetModuleFileNameA failed");
    return mew[0..res].dup;
  }
} else {
  extern(C) char* realpath(char* path, char* resolved_path = null);
  string myRealpath(string path) {
    return toString(realpath(toStringz(path)));
  }
}

int main(string[] args) {
  auto res = main2(args);
  // don't run final gc because we don't rely on that behavior
  exit(res);
  return res;
}

int main2(string[] args) {
  ast_math_constr();
  std.gc.disable();
  string execpath;
  scope(exit) save_cache();
  if ("/proc/self/exe".exists()) execpath = myRealpath("/proc/self/exe");
  else execpath = myRealpath(args[0]);
  execpath = execpath[0 .. execpath.rfind(pathsep) + 1];
  if (execpath.length) {
    include_path ~= execpath;
    include_path ~= Format(execpath, "..", sep, "include"); // assume .../[bin, include] structure
    // version(Windows) path_prefix = execpath;
  }
  initCastTable(); // NOT in static this!
  log_threads = false;
  // New(tp, 4);
  datalayout = "e-p:32:32:32-p1:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a128:128:128-a0:0:64-f80:32:32-n8:16:32-S128";
  auto exec = args.take();
  justAcceptedCallback = stuple(0, cast(typeof(sec())) 0) /apply/ (ref int prevHalfway, ref typeof(sec()) lastProg, string s) {
    
    auto info = lookupProgress(s);
    if (info._1.endsWith(EXT)) {
      foreach (path; include_path)
        if (auto rest = info._1.startsWith(path)) {
          if (auto rest2 = rest.startsWith(pathsep)) rest = rest2;
          info._1 = rest;
        }
      if (allowProgbar) {
        int proglen = ProgbarLength - info._1.length - 4;
        auto halfway = cast(int) (info._0 * proglen);
        if (halfway == prevHalfway) return;
        
        // rate limit
        auto t = sec();
        if (abs(t - lastProg) < 0.02) return;
        lastProg = t;
        
        prevHalfway = halfway;
        logSmart!(true) (info._1, "    ", renderProgbar(proglen, halfway));
      }
    }
  };
  string[] objects;
  // pre-pass
  {
    auto ar = args;
    while (ar.length) {
      auto arg = ar.take();
      if (arg == "-xpar") {
        xpar = ar.take().my_atoi();
        continue;
      }
      if (arg == "-xbreak") {
        xbreak = ar.take();
        continue;
      }
    }
  }
  auto ar = args;
  bool runMe;
  CompileSettings cs;
  if (isWindoze() || true) {
    // TODO: fix TLS under Windows (wtf is wrong with it!)
    cs.singlethread = true;
  }
  bool incremental;
  ar = processCArgs(ar);
  while (ar.length) {
    auto arg = ar.take();
    if (arg == "-break") {
      doBreak = true;
      continue;
    }
    if (arg == "-o") {
      output = ar.take();
      continue;
    }
    if (arg == "--loop" || arg == "-F") {
      incremental = true;
      cs.preopt = true; // makes incremental linking faster
      continue;
    }
    if (arg == "-sig") {
      sigmode = true;
      continue;
    }
    if (auto rest = arg.startsWith("-platform=")) {
      if (rest == "arm") rest = "arm-none-linux-gnueabi";
      platform_prefix = rest~"-";
      logln("Use platform '", platform_prefix, "'");
      foreach (ref entry; include_path) {
        if (entry == "/usr/include") {
          entry = "/usr/"~rest~"/include"; // fix up
        }
      }
      continue;
    }
    if (arg == "-save-temps" || arg == "-S") {
      cs.saveTemps = true;
      continue;
    }
    if (arg == "-O") {
      cs.optimize = true;
      continue;
    }
    if (arg == "-noprogress") {
      allowProgbar = false;
      continue;
    }
    if (arg == "-run") {
      runMe = true;
      continue;
    }
    if (arg == "-dump-info" || "parsers.txt".exists()) {
      write("parsers.txt", dumpInfo());
    }
    if (arg == "-g") {
      cs.debugMode = true;
      continue;
    }
    if (arg == "-pg") {
      cs.profileMode = true;
      linkerArgs ~= "-pg";
      continue;
    }
    if (arg == "-singlethread") {
      cs.singlethread = true;
      continue;
    }
    if (arg == "-release") {
      releaseMode = true;
      continue;
    }
    if (arg == "-xpar" || arg == "-xbreak") {
      ar.take();
      continue;
    }
    if (arg == "-dump-graphs") {
      genGraph("fcc.mods.dot", true, false);
      genGraph("fcc.classes.dot", false, true);
      genGraph("fcc.mixed.dot", true, true);
      genGraph("fcc.both.dot", true, true, false);
      continue;
    }
    if (arg == "-debug-parser") {
      verboseParser = true;
      continue;
    }
    if (arg == "-dump-xml") {
      dumpXMLRep = true;
      continue;
    }
    if (auto base = arg.endsWith(EXT)) {
      if (!output) output = base;
      if (isWindoze()) output ~= ".exe";
      if (!mainfile) mainfile = arg;
      if (!incremental) {
        try objects ~= arg.compileWithDepends(cs);
        catch (Exception ex) { logSmart!(false) (ex.toString()); return 1; }
      }
      continue;
    }
    logln("Invalid argument: ", arg);
    return 1;
  }
  if (!output) output = "exec";
  if (incremental) {
    incbuild(mainfile, cs, runMe);
    return 0;
  }
  objects.link(cs.optimize, cs.saveTemps);
  scope(exit) if (accesses.length) logln("access info: ", accesses);
  if (runMe) {
    auto cmd = "./"~output;
    version(Windows) cmd = output;
    logSmart!(false)("> ", cmd);
    auto res = system(toStringz(cmd));
    if (res < 256) return res;
    return (res & 0xff00) >> 8;
  }
  return 0;
}
