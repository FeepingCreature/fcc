module fcc; // feep's crazed compiler
// fcc is licensed under the terms of the GNU General Public License v3 or GPLv3.

import tools.log, tools.compat, tools.smart_import;
alias ast.types.Type Type;
import classgraph;

mixin(expandImport(`ast.[
  aggregate_parse, returns, ifstmt, loops, assign,
  structure, variable, fun, unary, arrays, index, slice,
  nestfun, structfuns, type_info, aliasing, oop, dg,
  newexpr, guard, withstmt, templ, globvars, context,
  concat, stringex, c_bind, eval, iterator[,_ext], properties,
  tuples, tuple_access, literal_string, literals, funcall, vector, externs,
  intr, conditionals, opers, conditional_opt, cond, casting,
  pointer, nulls, sa_index_opt, intrinsic, mode,
  propcall, properties_parse, main, alignment, modules_parse,
  platform, math, longmath, base, mixins, int_literal, static_arrays,
  enums, import_parse, pragmas, trivial, fp, expr_statement,
  typeset,
  macros, tenth, vardecl_expr, vardecl_parse, property, condprop],
  casts, optimizer_arm, optimizer_x86, optimizer_base`));

alias ast.tuples.resolveTup resolveTup;
// placed here to resolve circular dependency issues
import ast.parse, ast.namespace, ast.scopes;
// from ast.modules_parse
mixin DefaultParser!(gotNamed, "tree.expr.named", "24");

const ProgbarLength = 60;

string output;

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
    if (newarg) extra_linker_args ~= newarg;
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
    if (newarg) extra_linker_args ~= newarg;
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
// from ast.fun
static this() {
  // Assumption: SysInt is size_t.
  Expr fpeq(bool neg, Expr ex1, Expr ex2) {
    auto fp1 = fastcast!(FunctionPointer) (ex1.valueType()), fp2 = fastcast!(FunctionPointer) (ex2.valueType());
    if (!fp1 || !fp2) return null;
    return new CondExpr(new Compare(reinterpret_cast(Single!(SysInt), ex1), neg, false, true, false, reinterpret_cast(Single!(SysInt), ex2)));
  }
  Expr ptreq(bool neg, Expr ex1, Expr ex2) {
    auto p1 = fastcast!(Pointer) (ex1.valueType()), p2 = fastcast!(Pointer) (ex2.valueType());
    if (!p1 || !p2) return null;
    assert(p1.target == p2.target, Format("Cannot compare ", p1, " and ", p2));
    return new CondExpr(new Compare(reinterpret_cast(Single!(SysInt), ex1), neg, false, true, false, reinterpret_cast(Single!(SysInt), ex2)));
  }
  defineOp("==", false /apply/  &fpeq);
  defineOp("==", false /apply/ &ptreq);
  defineOp("!=",  true /apply/  &fpeq);
  defineOp("!=",  true /apply/ &ptreq);
  
  setupPropCall();
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
      res = buildFunCall(fastcast!(Function) (sysmod.lookup("_idiv")), mkTupleExpr(ex1, ex2), "_idiv");
    }
    if (isARM && op == "%" && nontrivial()) {
      res = buildFunCall(fastcast!(Function) (sysmod.lookup("_mod")), mkTupleExpr(ex1, ex2), "_mod");
    }
    if (!res) res = new AsmIntBinopExpr(ex1, ex2, op);
    if (b1 && b2) res = reinterpret_cast(fastcast!(IType) (sysmod.lookup("bool")), res);
    return res;
  }
  Expr handleIntUnary(string op, Expr ex) {
    if (!gotImplicitCast(ex, Single!(SysInt), &isInt))
      return null;
    return new AsmIntUnaryExpr(ex, op);
  }
  Expr handleLongUnary(string op, Expr ex) {
    if (!gotImplicitCast(ex, Single!(Long), &isLong))
      return null;
    return new AsmLongUnaryExpr(ex, op);
  }
  Expr handleNeg(Expr ex) {
    return lookupOp("-", mkInt(0), ex);
  }
  Expr handlePointerMath(string op, Expr ex1, Expr ex2) {
    auto ex22 = ex2;
    if (fastcast!(Pointer) (resolveTup(ex22.valueType()))) {
      if (op == "-") {
        return null; // wut
      }
      swap(ex1, ex2);
    }
    if (fastcast!(Pointer) (resolveTup(ex1.valueType()))) {
      if (isPointer(ex2.valueType())) return null;
      if (fastcast!(Float) (ex2.valueType())) {
        logln(ex1, " ", op, " ", ex2, "; WTF?! ");
        logln("is ", ex1.valueType(), " and ", ex2.valueType());
        // fail();
        throw new Exception("Invalid pointer op");
      }
      assert(!isFloat(ex2.valueType()));
      auto mul = (fastcast!(Pointer) (resolveTup(ex1.valueType()))).target.size;
      ex2 = handleIntMath("*", ex2, mkInt(mul));
      if (!ex2) return null;
      return reinterpret_cast(ex1.valueType(), handleIntMath(op, reinterpret_cast(Single!(SysInt), ex1), ex2));
    }
    return null;
  }
  Expr handleFloatMath(string op, Expr ex1, Expr ex2) {
    ex1 = foldex(ex1);
    ex2 = foldex(ex2);
    if (Single!(Double) == ex1.valueType() && !fastcast!(DoubleExpr) (ex1))
      return null;
    
    if (Single!(Double) == ex2.valueType() && !fastcast!(DoubleExpr) (ex2))
      return null;
    
    if (fastcast!(DoubleExpr)~ ex1 && fastcast!(DoubleExpr)~ ex2) return null;
    
    if (!gotImplicitCast(ex1, Single!(Float), &isFloat) || !gotImplicitCast(ex2, Single!(Float), &isFloat))
      return null;
    
    return new AsmFloatBinopExpr(ex1, ex2, op);
  }
  Expr handleDoubleMath(string op, Expr ex1, Expr ex2) {
    if (Single!(Double) != resolveTup(ex1.valueType())
     && Single!(Double) != resolveTup(ex2.valueType()))
      return null;
    if (!gotImplicitCast(ex1, Single!(Double), &isDouble) || !gotImplicitCast(ex2, Single!(Double), &isDouble))
      return null;
    
    return new AsmDoubleBinopExpr(ex1, ex2, op);
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
  (buildFunCall(fastcast!(Function) (sysmod.lookup("printf")), mkTupleExpr(mkString(s), ex), "mew")).emitAsm(af);
}

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
        (new Assignment(var, from, true)).emitAsm(af);
      });
    }
  }
}

// from ast.static_arrays
static this() {
  /*implicits ~= delegate Expr(Expr ex) {
    auto sa = fastcast!(StaticArray) (resolveType(ex.valueType()));
    if (!sa) return null;
    IType[] itlist;
    for (int i = 0; i < sa.length; ++i)
      itlist ~= sa.elemType;
    return reinterpret_cast(mkTuple(itlist), ex);
  };*/
}

extern(C)
void _line_numbered_statement_emitAsm(LineNumberedStatement lns, AsmFile af) {
  if (!af.debugMode) return;
  with (lns) {
    auto mod = current_module();
    string name; int line;
    lns.getInfo(name, line);
    if (!name) return;
    if (name.startsWith("<internal")) return;
    if (auto id = af.getFileId(name)) {
      // if (line >= 1) line -= 1; // wat!!
      af.put(".loc ", id, " ", line, " ", 0);
      if (!name.length) fail("TODO");
      af.put(comment(" being '"), name, "' at ", af.currentStackDepth);
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
  return new WithTempExpr(thing, dg);
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
  mod.iterate(&recurse);
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
string delegate(int, int*) compile(string file, CompileSettings cs) {
  scope(failure)
    logSmart!(false)("While compiling ", file);
  while (file.startsWith("./")) file = file[2 .. $];
  auto af = new AsmFile(cs.optimize, cs.debugMode, cs.profileMode, file);
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
  if (mod.alreadyEmat) return objname /apply/ (string objname, int total, int* complete) { return objname; }; // fresh
  if (mod.dontEmit) return null;
  fixupMain();
  auto len_parse = sec() - start_parse;
  double len_opt;
  len_opt = time({
    .postprocessModule(mod);
  }) / 1_000_000f;
  // verify(mod);
  auto len_gen = time({
    mod.emitAsm(af);
    if (!ematSysmod) {
      finalizeSysmod(mod);
      auto sysmodmod = fastcast!(Module) (sysmod);
      .postprocessModule(sysmodmod);
      sysmodmod.emitAsm(af);
      ematSysmod = true;
    }
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
  (string objname, string srcname, AsmFile af, Module mod, CompileSettings cs, int total, int* complete) {
    scope(exit)
      if (!cs.saveTemps)
        unlink(srcname.toStringz());
    scope f = new BufferedFile(srcname, FileMode.OutNew);
    auto len_emit = time({
      af.genAsm((string s) { f.write(cast(ubyte[]) s); });
    }) / 1_000_000f;
    f.close;
    string flags;
    if (!platform_prefix) flags = "--32";
    if (platform_prefix.startsWith("arm-")) flags = "-meabi=5";
    auto cmdline = Format(my_prefix(), "as ", flags, " -o ", objname, " ", srcname, " 2>&1");
    (*complete) ++;
    logSmart!(false)("> (", (*complete * 100) / total,  "% ", len_emit, "s) ", cmdline);
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

string delegate(int, int*)[] genCompilesWithDepends(string file, CompileSettings cs) {
  while (file.startsWith("./")) file = file[2 .. $];
  auto firstObj = compile(file, cs);
  auto modname = file.replace("/", ".")[0..$-3];
  string delegate(int, int*)[] dgs;
  bool[string] done;
  done["sys"] = true;
  Module[] todo;
  auto start = lookupMod(modname);
  
  todo ~= start.getAllModuleImports();
  todo ~= (fastcast!(Module) (sysmod)).getAllModuleImports();
  done[start.name] = true;
  dgs ~= firstObj;
  
  while (todo.length) {
    auto cur = todo.take();
    if (cur.name in done) continue;
    if (auto nuMod = compile(cur.name.replace(".", "/") ~ EXT, cs))
      dgs ~= nuMod;
    done[cur.name] = true;
    todo ~= cur.getAllModuleImports();
  }
  return dgs;
}

string[] compileWithDepends(string file, CompileSettings cs) {
  if (!emitpool && !cs.singlethread) emitpool = new Threadpool(4);
  auto dgs = file.genCompilesWithDepends(cs);
  string[] objs;
  auto complete = new int;
  void process(string delegate(int, int*) dg) { auto obj = dg(dgs.length, complete); synchronized objs ~= obj; }
  if (cs.singlethread) {
    foreach (dg; dgs) process(dg);
  } else {
    emitpool.mt_foreach(dgs, &process);
  }
  return objs;
}

void dumpXML() {
  void callback(ref Iterable it) {
    if (cast(NoOp) it) return;
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
  system(cmdline.toStringz());
}

import tools.threadpool;
Threadpool emitpool;

import std.file;
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
  bool needsRebuild(Module mod) {
    if (mod.dontEmit) return false;
    if (!isUpToDate(mod)) return true;
    foreach (mod2; mod.getAllModuleImports())
      if (needsRebuild(mod2)) return true;
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
    if (runMe) system(toStringz("./"~output));
  retry:
    pass1 = false;
    ematSysmod = false;
    initedSysmod = false;
    sysmod = null;
    checked = null;
    gotMain = null;
    resetTemplates();
    logln("please press return to continue. ");
    if (system("read")) return;
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
  string execpath;
  if ("/proc/self/exe".exists()) execpath = myRealpath("/proc/self/exe");
  else execpath = myRealpath(args[0]);
  execpath = execpath[0 .. execpath.rfind(pathsep) + 1];
  if (execpath.length) {
    include_path ~= execpath;
    include_path ~= Format(execpath, "..", sep, "include"); // assume .../[bin, include] structure
    version(Windows) path_prefix = execpath;
  }
  initCastTable(); // NOT in static this!
  log_threads = false;
  // New(tp, 4);
  /*
  logln("<?xml version=\"1.0\" ?><body>");
  scope(exit) logln("</body>");
  verboseXML = true;
  */
  auto exec = args.take();
  justAcceptedCallback = 0 /apply/ (ref int prevHalfway, string s) {
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
    if (arg == "-o") {
      output = ar.take();
      continue;
    }
    if (arg == "--loop" || arg == "-F") {
      willLoop = true;
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
      write("parsers.txt", parsecon.dumpInfo());
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
    if (arg == "-debug-parser-xml") {
      verboseXML = true;
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
  if (runMe) system(toStringz("./"~output));
  if (accesses.length) logln("access info: ", accesses);
  return 0;
}
