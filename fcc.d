module fcc; // feep's crazed compiler
// fcc is licensed under the terms of the GNU General Public License v3 or GPLv3.

import tools.log, tools.compat, tools.smart_import;
alias ast.types.Type Type;
import classgraph;

const string EXT = ".cr";

mixin(expandImport(`ast.[
  aggregate_parse, returns, ifstmt, loops, assign,
  structure, variable, fun, unary, arrays, index, slice,
  nestfun, structfuns, type_info, aliasing, oop, dg,
  newexpr, guard, withstmt, templ, globvars, context,
  concat, stringex, c_bind, eval, iterator[,_ext], properties,
  tuples, tuple_access, literal_string, funcall, vector, externs,
  intr, conditionals, opers, conditionals, cond, casting,
  pointer, nulls, unroll, sa_index_opt, intrinsic, mode,
  propcall, properties_parse, main, alignment, modules_parse,
  platform, base], casts`));

// placed here to resolve circular dependency issues
import ast.parse, ast.namespace, ast.scopes;
// from ast.namespace
mixin DefaultParser!(gotNamed, "tree.expr.named", "24");

static this() {
  New(namespace, { return cast(Namespace) null; });
  New(current_module, { return cast(Module) null; });
  // placed here because it needs some circular importage
  foldopt ~= delegate Expr(Expr ex) {
    auto mae = fastcast!(MemberAccess_Expr) (ex);
    if (!mae || mae.stm.name != "ptr") return null;
    
    auto rce = fastcast!(RCE) (mae.base);
    if (!rce) return null;
    if (!(rce.to in isArrayStructType)) return null;
    auto se = fastcast!(StringExpr) (rce.from);
    if (se) return se.getPointer();
    auto ar = fastcast!(ArrayMaker) (rce.from);
    if (ar) return ar.ptr;
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

extern(C)
void _line_numbered_statement_emitAsm(LineNumberedStatement lns, AsmFile af) {
  with (lns) {
    auto mod = current_module();
    if (auto id = af.getFileId(name)) {
      af.put(".loc ", id, " ", line);
      af.put("# being ", name);
    }
  }
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

string compile(string file, bool saveTemps = false, bool optimize = false, string configOpts = null) {
  while (file.startsWith("./")) file = file[2 .. $];
  auto af = new AsmFile(optimize, file);
  if (configOpts) {
    setupOpts();
    auto cmds = configOpts.split(",");
    foreach (cmd; cmds) {
      if (cmd == "info") {
        logSmart!(false)("count: ", opts.length);
        foreach (i, opt; opts) {
          logSmart!(false)("id:", i, " name:", opt._1, " ", opt._2?"on":"off");
        }
        exit(1);
      }
      if (auto rest = cmd.startsWith("disable ")) {
        int which = rest.atoi();
        opts[which]._2 = false;
        continue;
      }
    }
  }
  string srcname, objname;
  if (auto end = file.endsWith(EXT)) {
    srcname = end ~ ".s";
    objname = end ~ ".o";
  } else assert(false);
  scope(exit) {
    if (!saveTemps)
      unlink(srcname.toStringz());
  }
  auto modname = file.replace("/", ".")[0..$-3];
  auto start_parse = sec();
  auto mod = lookupMod(modname);
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
      extras.emitAsm(af);
    }
  }) / 1_000_000f;
  logSmart!(false)(len_parse, " to parse, ", len_opt, " to opt, ", len_gen, " to emit. ");
  Stuple!(string, float)[] entries;
  foreach (key, value; ast.namespace.bench) entries ~= stuple(key, value);
  entries.qsort(ex!("a, b -> a._1 > b._1"));
  float total = 0;
  foreach (entry; entries) total += entry._1;
  // logSmart!(false)("Subsegments: ", entries, "; total ", total);
  {
    scope f = new File(srcname, FileMode.OutNew);
    af.genAsm((string s) { f.write(cast(ubyte[]) s); });
    f.close;
  }
  auto cmdline = Format(platform_prefix, "as --32 -o ", objname, " ", srcname);
  logSmart!(false)("> ", cmdline);
  system(cmdline.toStringz()) == 0
    || assert(false, "Compilation failed! ");
  return objname;
}

string[] compileWithDepends(string file, bool saveTemps = false, bool optimize = false, string configOpts = null) {
  while (file.startsWith("./")) file = file[2 .. $];
  auto firstObj = compile(file, saveTemps, optimize, configOpts);
  auto modname = file.replace("/", ".")[0..$-3];
  string[] res;
  bool[string] done;
  done["sys"] = true;
  Module[] todo;
  auto start = lookupMod(modname);
  
  todo ~= start.imports;
  todo ~= sysmod.imports;
  done[start.name] = true;
  res ~= firstObj;
  
  while (todo.length) {
    auto cur = todo.take();
    if (cur.name in done) continue;
    res ~= compile(cur.name.replace(".", "/") ~ ".cr", saveTemps, optimize, configOpts);
    done[cur.name] = true;
    todo ~= cur.imports;
  }
  return res;
}

void link(string[] objects, string output, string[] largs, bool saveTemps = false) {
  scope(success)
    if (!saveTemps)
      foreach (obj; objects)
        unlink(obj.toStringz());
  string cmdline = platform_prefix~"gcc -m32 -o "~output~" ";
  foreach (obj; objects) cmdline ~= obj ~ " ";
  foreach (larg; largs) cmdline ~= larg ~ " ";
  logSmart!(false)("> ", cmdline);
  system(cmdline.toStringz());
}

import std.file;
void loop(string start, string output, string[] largs, bool optimize, bool runMe, bool saveTemps) {
  string toModule(string file) { return file.replace("/", ".").endsWith(".cr"); }
  string undo(string mod) {
    return mod.replace(".", "/") ~ ".cr";
  }
  void translate(string file, ref string obj, ref string src) {
    if (auto pre = file.endsWith(EXT)) {
      src = pre ~ ".s";
      obj = pre ~ ".o";
    } else assert(false);
  }
  static bool[string] alreadyBuilt;
  bool isUpToDate(string file) {
    if (!(file in alreadyBuilt)) {
      // rebuild at least once.
      // command line flags may have changed.
      return false;
    }
    string obj, src;
    file.translate(obj, src);
    if (!obj.exists()) return false;
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
  typeof(ast.modules.cache) precache;
  rereadMod = delegate bool(string mod) { return !mod.undo().isUpToDate(); };
  Module parse(string file, ref double len_parse, ref double len_opt, ref bool wasPresent) {
    void resetSysmod() {
      if (sysmod)
        sysmod.isValid = false;
      sysmod = null;
      setupSysmods();
    }
  
    auto modname = file.toModule();
    auto start_parse = sec();
    
    if (!isUpToDate(file)) {
      file.invalidate();
    }
    wasPresent = !!(modname in precache);
    
    if (file == start && !wasPresent)
      resetSysmod();
    auto mod = lookupMod(modname);
    len_parse = sec() - start_parse;
    len_opt = 0;
    if (!wasPresent) len_opt = time({ .postprocessModule(mod); }) / 1_000_000f;
    precache[modname] = mod; // lol why not dis?
    return mod;
  }
  void delegate() process(string file, string asmname, string objname, ref Module mod) {
    double len_opt, len_parse;
    bool wasDone;
    mod = parse(file, len_parse, len_opt, wasDone);
    if (wasDone) return null;
    return stuple(file, start, asmname, objname, mod, optimize, len_opt, len_parse, saveTemps) /apply/
    (string file, string start, string asmname, string objname, Module mod, bool optimize, double len_opt, double len_parse, bool saveTemps) {
      auto af = new AsmFile(optimize, file.toModule());
      alreadyBuilt[file] = true;
      scope(exit) if (!saveTemps) unlink (asmname.toStringz());
      auto len_gen = time({
        if (file == start) {
          finalizeSysmod(mod);
          .postprocessModule(sysmod);
          sysmod.emitAsm(af);
          void recurse(ref Iterable it) {
            if (auto sae = fastcast!(StatementAndExpr) (it)) sae.once = false;
            it.iterate(&recurse);
          }
          foreach (entry; extras.entries) {
            // reset for re-emit
            if (auto sae = fastcast!(StatementAndExpr) (entry)) sae.once = false;
            if (auto it = fastcast!(Iterable) (entry)) recurse(it);
          }
          ematSysmod = true;
        }
        mod.emitAsm(af);
        if (file == start) {
          extras.emitAsm(af);
        }
      }) / 1_000_000f;
      if (len_parse + len_opt + len_gen > 0.1)
        logSmart!(false)(file, ": ", len_parse, " to parse, ", len_opt, " to opt, ", len_gen, " to emit. ");
      scope f = new File(asmname, FileMode.OutNew);
      af.genAsm((string s) { f.write(cast(ubyte[]) s); });
      f.close;
      auto cmdline = Format(platform_prefix, "as --32 -o ", objname, " ", asmname);
      logSmart!(false)("> ", cmdline);
      system(cmdline.toStringz()) == 0
        || assert(false, "Compilation failed! ");
    };
  }
  void recursiveBuild(string file) {
    bool[string] objmap;
    bool recurse(string file) {
      string obj, src;
      file.translate(obj, src);
      Module mod;
      auto compile = file.process(src, obj, mod);
      bool anyChanged;
      foreach (entry; mod.imports)
        if (!(entry.name == "sys")) {
          logln("recurse ", file, " -> ", entry.name);
          auto didAlsoCompile = recurse(entry.name.undo());
          if (didAlsoCompile) anyChanged = true;
        }
      if (anyChanged && !compile) {
        file.invalidate();
        compile = file.process(src, obj, mod);
      }
      if (compile) compile();
      objmap[obj] = true;
      return !!compile;
    }
    recurse(file);
    auto objects = objmap.keys;
    objects.link(output, largs, true);
  }
  auto last = sec();
  precache = ast.modules.cache;
  while (true) {
    bool success = true;
    try recursiveBuild(start);
    catch (Exception ex) { logln(ex); success = false; }
    auto taken = sec() - last;
    if (success && runMe) {
      system(toStringz("./"~output));
    }
    if (success) precache = ast.modules.cache;
    logln(taken, " :please press return to continue. ");
    readln();
    last = sec();
  }
}

import assemble: debugOpts;
int main(string[] args) {
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
    if (info._1.endsWith(".cr")) {
      const Length = 50;
      auto progbar = new char[Length];
      auto halfway = cast(int) (info._0 * Length);
      if (halfway == prevHalfway) return;
      prevHalfway = halfway;
      for (int i = 0; i < Length; ++i) {
        if (i < halfway) progbar[i] = '=';
        else if (i == halfway) progbar[i] = '>';
        else progbar[i] = ' ';
      }
      logSmart!(true)(info._1, " \t [", progbar, "]");
    }
  };
  string[] objects;
  string output;
  auto ar = args;
  string[] largs;
  bool saveTemps, optimize, runMe;
  bool initedSysmod;
  void lazySysmod() {
    if (initedSysmod) return;
    initedSysmod = true;
    setupSysmods();
  }
  string configOpts;
  bool willLoop; string mainfile;
  while (ar.length) {
    auto arg = ar.take();
    if (arg == "-pthread") continue; // silently ignore;
    if (arg.startsWith("-D")) continue;
    if (arg == "-o") {
      output = ar.take();
      continue;
    }
    if (arg == "--loop" || arg == "-F") {
      logln("Don't use this. It's broken somehow. ");
      assert(false);
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
      continue;
    }
    if (auto rest = arg.startsWith("-I")) {
      rest = rest.strip();
      if (!rest.length) rest = ar.take();
      include_path = rest ~ include_path;
      continue;
    }
    if (arg == "-save-temps" || arg == "-S") {
      saveTemps = true;
      continue;
    }
    if (arg == "-O") {
      optimize = true;
      continue;
    }
    if (arg == "-debug-opts") {
      debugOpts = true;
      continue;
    }
    if (arg == "-run") {
      runMe = true;
      continue;
    }
    if (arg == "-config-opts") {
      configOpts = ar.take();
      continue;
    }
    if (arg == "-dump-info" || "parsers.txt".exists()) {
      write("parsers.txt", parsecon.dumpInfo());
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
    if (auto base = arg.endsWith(".cr")) {
      if (!output) output = base;
      if (!mainfile) mainfile = arg;
      if (!willLoop) {
        lazySysmod();
        try objects ~= arg.compileWithDepends(saveTemps, optimize, configOpts);
        catch (Exception ex) { logln(ex.toString()); return 1; }
      }
      continue;
    }
    logln("Invalid argument: ", arg);
    return 1;
  }
  if (!output) output = "exec";
  if (willLoop) {
    loop(mainfile, output?output:"exec", largs, optimize, runMe, saveTemps);
    return 0;
  }
  objects.link(output, largs, saveTemps);
  if (runMe) system(toStringz("./"~output));
  return 0;
}
