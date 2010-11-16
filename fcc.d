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
  pointer, nullcasts]`));

// placed here to resolve circular dependency issues
import ast.parse, ast.namespace, ast.scopes;
// from ast.namespace
mixin DefaultParser!(gotNamed, "tree.expr.named", "24");

static this() {
  New(namespace, { return cast(Namespace) null; });
  New(current_module, { return cast(Module) null; });
}
alias ast.parse.startsWith startsWith;
// from ast.fun
static this() {
  // Assumption: SysInt is size_t.
  Expr fpeq(bool neg, Expr ex1, Expr ex2) {
    auto fp1 = cast(FunctionPointer) ex1.valueType(), fp2 = cast(FunctionPointer) ex2.valueType();
    if (!fp1 || !fp2) return null;
    return new CondExpr(new Compare(reinterpret_cast(Single!(SysInt), ex1), neg, false, true, false, reinterpret_cast(Single!(SysInt), ex2)));
  }
  Expr ptreq(bool neg, Expr ex1, Expr ex2) {
    auto p1 = cast(Pointer) ex1.valueType(), p2 = cast(Pointer) ex2.valueType();
    if (!p1 || !p2) return null;
    assert(p1.target == p2.target, Format("Cannot compare ", p1, " and ", p2));
    return new CondExpr(new Compare(reinterpret_cast(Single!(SysInt), ex1), neg, false, true, false, reinterpret_cast(Single!(SysInt), ex2)));
  }
  defineOp("==", false /apply/  &fpeq);
  defineOp("==", false /apply/ &ptreq);
  defineOp("!=",  true /apply/  &fpeq);
  defineOp("!=",  true /apply/ &ptreq);
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

void optimize(Module mod) { ast.fold.opt(mod); }

bool ematSysmod;

string compile(string file, bool saveTemps = false, bool optimize = false, string configOpts = null) {
  auto af = new AsmFile(optimize, file.replace("/", "_").replace(".cr", ""));
  if (configOpts) {
    setupOpts();
    auto cmds = configOpts.split(",");
    foreach (cmd; cmds) {
      if (cmd == "info") {
        writefln("count: ", opts.length);
        foreach (i, opt; opts) {
          writefln("id:", i, " name:", opt._1, " ", opt._2?"on":"off");
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
  auto len_parse = sec() - start_parse;
  double len_opt;
  len_opt = time({
    if (!ematSysmod)
      .optimize(sysmod);
    .optimize(mod);
  }) / 1_000_000f;
  auto len_gen = time({
    if (!ematSysmod) {
      sysmod.emitAsm(af);
      ematSysmod = true;
    }
    mod.emitAsm(af);
  }) / 1_000_000f;
  writefln(len_parse, " to parse, ", len_opt, " to opt, ", len_gen, " to emit. ");
  Stuple!(string, float)[] entries;
  foreach (key, value; ast.namespace.bench) entries ~= stuple(key, value);
  entries.qsort(ex!("a, b -> a._1 > b._1"));
  float total = 0;
  foreach (entry; entries) total += entry._1;
  writefln("Subsegments: ", entries, "; total ", total);
  {
    scope f = new File(srcname, FileMode.OutNew);
    af.genAsm((string s) { f.write(cast(ubyte[]) s); });
    f.close;
  }
  auto cmdline = Format("as --32 -o ", objname, " ", srcname);
  writefln("> ", cmdline);
  system(cmdline.toStringz()) == 0
    || assert(false, "Compilation failed! ");
  return objname;
}

void link(string[] objects, string output, string[] largs, bool saveTemps = false) {
  scope(success)
    if (!saveTemps)
      foreach (obj; objects)
        unlink(obj.toStringz());
  string cmdline = "gcc -m32 -o "~output~" ";
  foreach (obj; objects) cmdline ~= obj ~ " ";
  foreach (larg; largs) cmdline ~= larg ~ " ";
  writefln("> ", cmdline);
  system(cmdline.toStringz());
}

import assemble: debugOpts;
int main(string[] args) {
  log_threads = false;
  /*
  logln("<?xml version=\"1.0\" ?><body>");
  scope(exit) logln("</body>");
  verboseXML = true;
  */
  auto exec = args.take();
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
  while (ar.length) {
    auto arg = ar.take();
    if (arg == "-o") {
      output = ar.take();
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
    if (auto rest = arg.startsWith("-I").strip()) {
      if (!rest.length) rest = ar.take();
      include_path ~= rest;
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
    if (auto base = arg.endsWith(".cr")) {
      if (!output) output = arg[0 .. $-3];
      lazySysmod();
      try objects ~= arg.compile(saveTemps, optimize, configOpts);
      catch (Exception ex) { logln(ex.toString()); return 1; }
      continue;
    }
    logln("Invalid argument: ", arg);
    return 1;
  }
  if (!output) output = "exec";
  objects.link(output, largs, saveTemps);
  if (runMe) system(toStringz("./"~output));
  return 0;
}
