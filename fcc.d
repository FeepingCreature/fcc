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
  platform, longmath, base, mixins, int_literal, static_arrays,
  enums, import_parse, pragmas, trivial, fp, expr_statement,
  macros, tenth, vardecl_expr, property],
  casts`));

// placed here to resolve circular dependency issues
import ast.parse, ast.namespace, ast.scopes;
// from ast.modules_parse
mixin DefaultParser!(gotNamed, "tree.expr.named", "24");

const ProgbarLength = 60;

string output;

static this() {
  // Link with this library
  pragmas["lib"] = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, (Expr ex) {
      return !!fastcast!(StringExpr) (foldex(ex));
    }))
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
  pragmas["binary"] = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, (Expr ex) {
      return !!fastcast!(StringExpr) (foldex(ex));
    }))
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
  New(current_module, { return cast(Module) null; });
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
      if (line >= 1) line -= 1; // wat!!
      af.put(".loc ", id, " ", line, " ", 0);
      if (!name.length) fail("TODO");
      af.put("# being '", name, "' at ", af.currentStackDepth);
    }
  }
}


// from ast.vardecl
extern(C) Expr tmpize_maybe(Expr thing, E2Edg dg) {
  if (auto ea = fastcast!(ExprAlias) (thing)) thing = ea.base;
  if (fastcast!(Variable) (thing)) return dg(thing); // cheap to emit
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
import optimizer, ast.fold;

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
  ast.fold.opt(mod);
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
  bool saveTemps, optimize, debugMode, profileMode;
  string configOpts;
}

extern(C) int mkdir(char*, int);
string delegate(int, int*) compile(string file, CompileSettings cs) {
  while (file.startsWith("./")) file = file[2 .. $];
  auto af = new AsmFile(cs.optimize, cs.debugMode, cs.profileMode, file);
  af.processorExtensions["sse3"] = true;
  if (cs.configOpts) {
    setupOpts();
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
  if (mod.alreadyEmat) return objname /apply/ (string objname, int total, int* complete) { return objname; }; // fresh
  if (mod.dontEmit) return null;
  fixupMain();
  auto len_parse = sec() - start_parse;
  double len_opt;
  len_opt = time({
    .postprocessModule(mod);
  }) / 1_000_000f;
  auto len_gen = time({
    mod.emitAsm(af);
    if (!ematSysmod) {
      finalizeSysmod(mod);
      .postprocessModule(sysmod);
      sysmod.emitAsm(af);
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
    auto cmdline = Format(platform_prefix, "as --32 -o ", objname, " ", srcname, " 2>&1");
    (*complete) ++;
    logSmart!(false)("> (", (*complete * 100) / total,  "% ", len_emit, "s) ", cmdline);
    if (system(cmdline.toStringz())) {
      logln("ERROR: Compilation failed! ");
      exit(1);
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
  
  todo ~= start.getImports();
  todo ~= sysmod.getImports();
  done[start.name] = true;
  dgs ~= firstObj;
  
  while (todo.length) {
    auto cur = todo.take();
    if (cur.name in done) continue;
    if (auto nuMod = compile(cur.name.replace(".", "/") ~ EXT, cs))
      dgs ~= nuMod;
    done[cur.name] = true;
    todo ~= cur.getImports();
  }
  return dgs;
}

string[] compileWithDepends(string file, CompileSettings cs) {
  if (!emitpool) emitpool = new Threadpool(4);
  auto dgs = file.genCompilesWithDepends(cs);
  string[] objs;
  auto complete = new int;
  void process(string delegate(int, int*) dg) { auto obj = dg(dgs.length, complete); synchronized objs ~= obj; }
  emitpool.mt_foreach(dgs, &process);
  return objs;
}

void link(string[] objects, string[] largs, bool saveTemps = false) {
  scope(success)
    if (!saveTemps)
      foreach (obj; objects)
        unlink(obj.toStringz());
  string cmdline = platform_prefix~"gcc -m32 -o "~output~" ";
  foreach (obj; objects) cmdline ~= obj ~ " ";
  foreach (larg; largs ~ extra_linker_args) cmdline ~= larg ~ " ";
  logSmart!(false)("> ", cmdline);
  system(cmdline.toStringz());
}

import tools.threadpool;
Threadpool emitpool;

import std.file;
void loop(string start, string[] largs,
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
    foreach (imp; mod.getImports())
      if (needsRebuild(imp)) return true;
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
      objs.link(largs, true);
    } catch (Exception ex) {
      logln(ex);
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

extern(C) char* realpath(char* path, char* resolved_path = null);

import assemble: debugOpts;
int main(string[] args) {
  string execpath;
  if ("/proc/self/exe".exists()) execpath = toString(realpath("/proc/self/exe"));
  else execpath = toString(realpath(toStringz(args[0])));
  execpath = execpath[0 .. execpath.rfind("/") + 1];
  if (execpath.length)
    include_path ~= execpath;
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
          if (auto rest2 = rest.startsWith("/")) rest = rest2;
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
  string[] largs;
  bool runMe;
  CompileSettings cs;
  bool willLoop;
  while (ar.length) {
    auto arg = ar.take();
    if (arg == "-pthread") continue; // silently ignore;
    if (arg.startsWith("-D")) continue;
    if (arg == "-o") {
      output = ar.take();
      continue;
    }
    if (arg == "--loop" || arg == "-F") {
      willLoop = true;
      continue;
    }
    if (auto rest = arg.startsWith("-l").strip()) {
      if (!rest.length) rest = ar.take();
      largs ~= "-l"~rest;
      continue;
    }
    if (auto rest = arg.startsWith("-L").strip()) {
      if (!rest.length) rest = ar.take();
      largs ~= "-L"~rest;
      continue;
    }
    if (auto rest = arg.startsWith("-Wl")) {
      rest.accept(",");
      rest = rest.strip();
      if (!rest.length) rest = ar.take();
      largs ~= rest;
      continue;
    }
    if (auto rest = arg.startsWith("-platform=")) {
      platform_prefix = rest~"-";
      logln("Use platform '", platform_prefix, "'");
      foreach (ref entry; include_path) {
        if (entry == "/usr/include") {
          entry = "/usr/"~rest~"/include"; // fix up
        }
      }
      continue;
    }
    if (auto rest = arg.startsWith("-I")) {
      rest = rest.strip();
      if (!rest.length) rest = ar.take();
      include_path = rest ~ include_path;
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
      largs ~= "-pg";
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
        catch (Exception ex) { logln(ex.toString()); return 1; }
      }
      continue;
    }
    logln("Invalid argument: ", arg);
    return 1;
  }
  if (!output) output = "exec";
  if (willLoop) {
    loop(mainfile, largs, cs, runMe);
    return 0;
  }
  objects.link(largs, cs.saveTemps);
  if (runMe) system(toStringz("./"~output));
  if (accesses.length) logln("access info: ", accesses);
  return 0;
}
