module fcc; // feep's crazed compiler
// fcc is licensed under the terms of the GNU General Public License v3 or GPLv3.

import tools.log, tools.compat;
alias ast.types.Type Type;
import classgraph;

const string EXT = ".cr";

import
  ast.aggregate, ast.returns, ast.ifstmt, ast.loops, ast.assign,
  ast.structure, ast.variable, ast.fun, ast.unary,
  ast.arrays, ast.index, ast.slice, ast.nestfun,
  ast.structfuns, ast.type_info, ast.aliasing,
  ast.oop, ast.dg, ast.newexpr, ast.guard, ast.withstmt,
  ast.templ, ast.globvars, ast.context, ast.concat,
  ast.stringex, ast.c_bind;

// placed here to resolve circular dependency issues
import ast.parse, ast.namespace, ast.scopes;
// from ast.namespace
mixin DefaultParser!(gotNamed, "tree.expr.named", "4");
static this() { New(namespace, { return cast(Namespace) null; }); }
alias ast.parse.startsWith startsWith;

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

import tools.time;
import optimizer;
string compile(string file, bool saveTemps = false, bool optimize = false, string configOpts = null) {
  auto af = new AsmFile(optimize);
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
  auto text = file.read().castLike("");
  Module mod;
  // if (!text.gotModule(mod)) assert(false, "unable to eat module from "~file~": "~error);
  auto start_parse = sec();
  if (auto mt = parsecon.parse(text, "tree.module"))
    mod = cast(Module) mt;
  else assert(false, "unable to eat module from "~file~": "~error);
  auto len_parse = sec() - start_parse;
  if (text.strip().length) assert(false, "this text confuses me: "~text.next_text()~": "~error);
  auto len_gen = time({sysmod.emitAsm(af); mod.emitAsm(af); }) / 1_000_000f;
  writefln(len_parse, " to parse, ", len_gen, " to emit. ");
  writefln("Subsegments: ", ast.namespace.bench);
  srcname.write(af.genAsm());
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

void init() {
  genGraph("fcc.mods.dot", true, false);
  genGraph("fcc.classes.dot", false, true);
  genGraph("fcc.mixed.dot", true, true);
  genGraph("fcc.both.dot", true, true, false);
  write("parsers.txt", parsecon.dumpInfo());
}

import assemble: debugOpts;
int main(string[] args) {
  /*
  log_threads = false;
  logln("<?xml version=\"1.0\" ?><body>");
  scope(exit) logln("</body>");
  verboseXML = true;
  */
  init();
  auto exec = args.take();
  string[] objects;
  string output;
  auto ar = args;
  string[] largs;
  bool saveTemps, optimize;
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
    if (arg.startsWith("-l")) {
      largs ~= arg;
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
    if (arg == "-config-opts") {
      configOpts = ar.take();
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
      objects ~= arg.compile(saveTemps, optimize, configOpts);
      continue;
    }
    logln("Invalid argument: ", arg);
    return 1;
  }
  if (!output) output = "exec";
  objects.link(output, largs, saveTemps);
  return 0;
}
