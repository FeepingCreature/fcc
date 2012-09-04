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
  concat, stringex, c_bind, eval, iterator[,_ext], properties,
  tuples, tuple_access, literal_string, literals, funcall, vector, externs,
  intr, conditionals, opers, conditional_opt, cond, casting,
  pointer, nulls, sa_index_opt, intrinsic, mode, repl,
  propcall, properties_parse, main, alignment, modules_parse,
  platform, math, longmath, base, mixins, int_literal, static_arrays,
  enums, import_parse, pragmas, trivial, fp, expr_statement,
  typeset, dependency, prefixfun,
  macros, tenth, vardecl_expr, vardecl_parse, property, condprop],
  casts, optimizer_arm, optimizer_x86, optimizer_base`));

alias ast.tuples.resolveTup resolveTup;
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

static this() {
  New(optimizer_x86.cachething);
  New(optimizer_x86.proctrack_cachething);
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

extern(C) void rt_print(AsmFile af, string s) {
  auto printf = sysmod.lookup("printf");
  buildFunCall(printf, mkString(s~"\n"), "printf").emitAsm(af);
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
static this() {
  bool isInt(IType it) { return test(Single!(SysInt) == it); }
  bool isFloat(IType it) { return test(Single!(Float) == it); }
  bool isDouble(IType it) { return test(Single!(Double) == it); }
  bool isLong(IType it) { return test(Single!(Long) == it); }
  bool isPointer(IType it) { return test(fastcast!(Pointer)~ it); }
  bool isBool(IType it) { return test(it == fastcast!(IType) (sysmod.lookup("bool"))); }
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
    if (isARM && op == "/" && nontrivial()) {
      if (!sysmod.lookup("_idiv")) {
        logln("too early for division");
        fail;
      }
      res = buildFunCall(sysmod.lookup("_idiv"), mkTupleExpr(ex1, ex2), "_idiv");
    }
    if (isARM && op == "%" && nontrivial()) {
      res = buildFunCall(sysmod.lookup("_mod"), mkTupleExpr(ex1, ex2), "_mod");
    }
    if (!res) res = fastalloc!(AsmIntBinopExpr)(ex1, ex2, op);
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
        return null; // wut
      }
      swap(ex1, ex2);
      e1pt = p;
    }
    if (!e1pt) e1pt = fastcast!(Pointer) (resolveTup(ex1.valueType()));
    if (!e1pt) return null;
    if (isPointer(ex2.valueType())) return null;
    if (fastcast!(Float) (ex2.valueType())) {
      logln(ex1, " ", op, " ", ex2, "; WTF?! ");
      logln("is ", ex1.valueType(), " and ", ex2.valueType());
      // fail();
      throw new Exception("Invalid pointer op");
    }
    if (auto ie = fastcast!(IntExpr) (ex2)) { // shortcut
      ex2 = mkInt(ie.num * e1pt.target.size);
    } else {
      ex2 = handleIntMath("*", ex2, mkInt(e1pt.target.size));
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

extern(C) void printThing(AsmFile af, string s, Expr ex) {
  (buildFunCall(sysmod.lookup("printf"), mkTupleExpr(mkString(s), ex), "mew")).emitAsm(af);
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


// from ast.scopes
extern(C) void genRetvalHolder(Scope sc) {
  if (!sc.lookup("__retval_holder", true)) {
    auto ret = sc.get!(Function).type.ret;
    if (!ret) return;
    if (ret != Single!(Void)) {
      auto var = fastalloc!(Variable)(ret, "__retval_holder", boffs(ret));
      auto vd = fastalloc!(VarDecl)(var);
      sc.addStatement(vd);
      sc.add(var);
    }
  }
}

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
import asmfile, ast.vardecl;
extern(C) void _reinterpret_cast_expr(RCE rce, AsmFile af) {
  with (rce) {
    int size = to.size;
    if (Single!(Void) == to) size = 0;
    mixin(mustOffset("size"));
    auto fromtype = from.valueType();
    auto depth = af.currentStackDepth + fromtype.size;
    doAlign(depth, fromtype);
    if (depth == af.currentStackDepth + fromtype.size) {
      from.emitAsm(af);
    } else {
      mkVarUnaligned(af, to, true, (Variable var) {
        (fastalloc!(Assignment)(var, from, true)).emitAsm(af);
      });
    }
  }
}

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
              mcl = lookupOp("*", e1l, mkInt(a1.elemType.size));
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
  auto sc = new Scope;
  sc.configPosition(text);
  
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  auto t2 = text;
  Statement _body;
  if (rest(t2, "tree.stmt", &_body)) { text = t2; sc.addStatement(_body); return sc; }
  t2.failparse("Couldn't match scope");
}
mixin DefaultParser!(gotScope, "tree.scope");


extern(C)
void _line_numbered_statement_emitAsm(LineNumberedStatement lns, AsmFile af) {
  with (lns) {
    string name; int line;
    lns.getInfo(name, line);
    if (!name) return;
    if (name.startsWith("<internal")) return;
    if (auto id = af.getFileId(name)) {
      if (af.debugMode) {
        af.put(".loc ", id, " ", line, " ", 0);
        if (!name.length) fail("TODO");
        af.put(comment(" being '"), name, "' at ", af.currentStackDepth);
      }
      version(CustomDebugInfo) if (auto fun = current_emitting_function()) {
        fun.add_line_number(af, line);
      }
    }
  }
}

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
    if (fastcast!(OffsetExpr) (ex))
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
extern(C) Expr _tmpize_maybe(Expr thing, E2EOdg dg, bool force) {
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

void postprocessModule(Module mod) {
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
    it.iterate(&recurse);
  }
  if (isWindoze()) mod.iterate(&recurse);
  // result: mostly below 7
  // gatherSizeStats(mod);
}

bool ematSysmod;

bool initedSysmod;
void lazySysmod() {
  if (initedSysmod) return;
  initedSysmod = true;
  setupSysmods();
}

bool allowProgbar = true;

struct CompileSettings {
  bool saveTemps, optimize, debugMode, profileMode, singlethread;
  string configOpts;
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

extern(C) int mkdir(char*, int);
string delegate() compile(string file, CompileSettings cs) {
  scope(failure)
    logSmart!(false)("While compiling ", file);
  while (file.startsWith("./")) file = file[2 .. $];
  auto af = fastalloc!(AsmFile)(cs.optimize, cs.debugMode, cs.profileMode, file);
  if (!isARM) af.processorExtensions["sse3"] = true;
  setupGenericOpts();
  if (isARM) setupARMOpts();
  else setupX86Opts();
  if (cs.configOpts) {
    auto cmds = cs.configOpts.split(",");
    foreach (cmd; cmds) {
      if (cmd == "info") {
        logln("count: ", opts.length);
        foreach (i, opt; opts) {
          logln("id:", i, " name:", opt._1, " ", opt._2?"on":"off");
        }
        exit(1);
      }
      if (auto rest = cmd.startsWith("disable ")) {
        int which = rest.my_atoi();
        opts[which]._2 = false;
        continue;
      }
    }
  }
  lazySysmod();
  string srcname, objname;
  if (auto end = file.endsWith(EXT)) {
    srcname = ".obj/" ~ end ~ ".s";
    objname = ".obj/" ~ end ~ ".o";
    auto path = srcname[0 .. srcname.rfind("/")];
    string mew = ".";
    foreach (component; path.split("/")) {
      mew = mew.sub(component);
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
  if (mod.alreadyEmat) return objname /apply/ (string objname) { return objname; }; // fresh
  if (mod.dontEmit) return null;
  fixupMain();
  auto len_parse = sec() - start_parse;
  double len_opt;
  len_opt = time({
    .postprocessModule(mod);
  }) / 1_000_000f;
  // verify(mod);
  // finalizeSysmod(mod);
  auto len_gen = time({
    mod.emitAsm(af);
  }) / 1_000_000f;
  // logSmart!(false)(len_parse, " to parse, ", len_opt, " to optimize. ");
  Stuple!(string, float)[] entries;
  foreach (key, value; ast.namespace.bench) entries ~= stuple(key, value);
  entries.qsort(ex!("a, b -> a._1 > b._1"));
  float total = 0;
  foreach (entry; entries) total += entry._1;
  // logSmart!(false)("Subsegments: ", entries, "; total ", total);
  mod.alreadyEmat = true;
  return stuple(objname, srcname, af, mod, cs) /apply/
  (string objname, string srcname, AsmFile af, Module mod, CompileSettings cs) {
    scope(exit)
      if (!cs.saveTemps)
        unlink(srcname.toStringz());
    scope f = fastalloc!(BufferedFile)(srcname, FileMode.OutNew);
    auto len_emit = time({
      af.genAsm((string s) { f.write(cast(ubyte[]) s); });
    }) / 1_000_000f;
    f.close;
    string flags;
    if (!platform_prefix || platform_prefix.endsWith("-mingw32-"))
      flags = "--32";
    if (platform_prefix.startsWith("arm-")) flags = "-meabi=5";
    auto cmdline = Format(my_prefix(), "as ", flags, " -o ", objname, " ", srcname, " 2>&1");
    logSmart!(false)("> (", len_emit, "s) ", cmdline);
    synchronized {
      if (system(cmdline.toStringz())) {
        logln("ERROR: Compilation failed! ");
        exit(1);
      }
    }
    mod.alreadyEmat = true;
    return objname;
  };
}

void genCompilesWithDepends(string file, CompileSettings cs, void delegate(string delegate()) assemble) {
  while (file.startsWith("./")) file = file[2 .. $];
  auto firstObj = compile(file, cs);
  auto modname = file.replace("/", ".")[0..$-3];
  bool[string] done;
  Module[] todo;
  auto start = lookupMod(modname);
  finalizeSysmod(start);
  
  todo ~= start.getAllModuleImports();
  done[start.name] = true;
  assemble(firstObj);
  
  while (todo.length) {
    auto cur = todo.take();
    if (cur.name in done) continue;
    if (auto nuMod = compile(cur.name.replace(".", "/") ~ EXT, cs))
      assemble(nuMod);
    done[cur.name] = true;
    todo ~= cur.getAllModuleImports();
  }
}

string[] compileWithDepends(string file, CompileSettings cs) {
  string[] objs;
  int waits;
  auto seph = new Semaphore;
  void process(string delegate() dg) {
    if (cs.singlethread) objs ~= dg();
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

void link(string[] objects, bool saveTemps = false) {
  if (dumpXMLRep) dumpXML();
  scope(success)
    if (!saveTemps)
      foreach (obj; objects)
        unlink(obj.toStringz());
  string linkflags = "-m32 -Wl,--gc-sections -L/usr/local/lib";
  string cmdline = my_prefix()~"gcc "~linkflags~" -o "~output~" ";
  foreach (obj; objects) cmdline ~= obj ~ " ";
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

import memconserve_stdfile;
alias memconserve_stdfile.exists exists;
alias memconserve_stdfile.getTimes getTimes;
void loop(string start,
          CompileSettings cs, bool runMe)
{
  string toModule(string file) { return file.replace("/", ".").endsWith(EXT); }
  string undo(string mod) {
    return mod.replace(".", "/") ~ EXT;
  }
  void translate(string file, ref string obj, ref string src) {
    if (auto pre = file.endsWith(EXT)) {
      src = ".obj/" ~ pre ~ ".s";
      obj = ".obj/" ~ pre ~ ".o";
    } else assert(false);
  }
  bool isUpToDate(Module mod) {
    auto file = mod.name.undo();
    string obj, src;
    file.translate(obj, src);
    if (!obj.exists()) return false;
    if (!file.exists()) {
      foreach (entry; include_path)
        if (entry.sub(file).exists()) { file = entry.sub(file); break; }
    }
    long created1, accessed1, modified1, created2, accessed2, modified2;
    file.getTimes(created1, accessed1, modified1);
    obj.getTimes(created2, accessed2, modified2);
    return modified1 < modified2;
  }
  void invalidate(string file) {
    auto modname = file.toModule();
    if (auto p = modname in ast.modules.cache) {
      p.isValid = false;
    }
    ast.modules.cache.remove(modname);
  }
  bool[string] checked;
  bool[string] checking;
  bool needsRebuild(Module mod) {
    // logln("needsRebuild? ", mod.name, " ", mod.dontEmit, " ", mod is sysmod, " ", isUpToDate(mod), " ", !!(mod.name in checking), " ", mod.getAllModuleImports());
    if (mod.dontEmit) return false;
    if (mod is sysmod || !isUpToDate(mod)) return true;
    if (mod.name in checking) return false; // break the circle
    checking[mod.name] = true;
    scope(exit) checking.remove(mod.name);
    foreach (mod2; mod.getAllModuleImports())
      if (mod2 !is sysmod && needsRebuild(mod2)) return true;
    return false;
  }
  bool pass1 = true;
  rereadMod = delegate bool(Module mod) {
    if (pass1) return false;
    if (mod.name in checked) return false;
    auto res = needsRebuild(mod);
    checked[mod.name] = true;
    return res;
  };
  while (true) {
    lazySysmod();
    try {
      string[] objs = start.compileWithDepends(cs);
      objs.link(true);
    } catch (Exception ex) {
      logSmart!(false) (ex);
      goto retry;
    }
    if (runMe) {
      auto cmd = "./"~output;
      version(Windows) cmd = output;
      logSmart!(false)("> ", cmd); system(toStringz(cmd));
    }
  retry:
    pass1 = false;
    checked = null;
    checking = null;
    gotMain = null;
    resetTemplates();
    version(Windows) { if (system("pause")) return; }
    else {
      if (!sigmode) {
        logln("please press return to continue. ");
        if (system("read"))
          return;
      } else {
        logln("Waiting for refcc");
        sigset_t waitset;
        
        sigemptyset(&waitset);
        sigaddset(&waitset, SIGXCPU);
        sigprocmask(SIG_BLOCK, &waitset, null);
        int sig;
        sigwait(&waitset, &sig);
      }
    }
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

import assemble: debugOpts;
int main(string[] args) {
  // std.gc.disable();
  string execpath;
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
  auto exec = args.take();
  justAcceptedCallback = stuple(0, cast(typeof(sec())) 0) /apply/ (ref int prevHalfway, ref typeof(sec()) lastProg, string s) {
    // rate limit
    auto t = sec();
    if (abs(t - lastProg) < 0.02) return;
    lastProg = t;
    
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
    }
  }
  auto ar = args;
  bool runMe;
  CompileSettings cs;
  bool willLoop;
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
      willLoop = true;
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
    if (arg == "-debug-opts") {
      debugOpts = true;
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
    if (arg == "-config-opts") {
      cs.configOpts = ar.take();
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
    if (arg == "-xpar") {
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
      if (!willLoop) {
        try objects ~= arg.compileWithDepends(cs);
        catch (Exception ex) { logSmart!(false) (ex.toString()); return 1; }
      }
      continue;
    }
    logln("Invalid argument: ", arg);
    return 1;
  }
  if (!output) output = "exec";
  if (willLoop) {
    loop(mainfile, cs, runMe);
    return 0;
  }
  objects.link(cs.saveTemps);
  if (runMe) {
	auto cmd = "./"~output;
	version(Windows) cmd = output;
	logSmart!(false)("> ", cmd); system(toStringz(cmd));
  }
  if (accesses.length) logln("access info: ", accesses);
  return 0;
}
