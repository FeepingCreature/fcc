module fcc; // feep's crazed compiler

import tools.base, tools.log, tools.compat;

extern(C) {
  int mkstemp(char* tmpl);
  int close(int fd);
}

string tmpnam(string base = "fcc") {
  string name = base ~ "XXXXXX";
  auto p = toStringz(name);
  auto fd = mkstemp(p);
  assert(fd != -1);
  close(fd);
  return toString(p);
}

bool isAlpha(dchar d) {
  // TODO expand
  return d >= 'A' && d <= 'Z' || d >= 'a' && d <= 'z';
}

bool isAlphanum(dchar d) {
  return isAlpha(d) || d >= '0' && d <= '9';
}

bool accept(ref string s, string t) {
  auto s2 = s.strip();
  t = t.strip();
  // logln("accept ", t, " from ", s2, "? ", !!s2.startsWith(t));
  return s2.startsWith(t) && (s = s2[t.length .. $], true);
}

/+
  What do we expect of a type system?
  Nothing.
+/

enum Type {
  None = -1,
  Void,
  CharPtr
}

class ParseException {
  string where, info;
  this(string where, string info) {
    this.where = where; this.info = info;
  }
}

bool gotType(ref string text, out Type type) {
  if (text.accept("void")) return type = Type.Void, true;
  return false;
}

struct AsmFile {
  ubyte[][string] constants;
  string code;
  void loadStack(string addr) {
    code ~= Format("movl "~addr~", (%esp)\n");
  }
  void put(T...)(T t) {
    code ~= Format(t, "\n");
  }
  string genAsm() {
    string res;
    res ~= ".data\n";
    foreach (name, c; constants) {
      res ~= Format(name, ":\n");
      res ~= ".byte ";
      foreach (val; c) res ~= Format(cast(ubyte) val, ", ");
      res ~= "0\n";
    }
    res ~= ".text\n";
    res ~= code;
    return res;
  }
}

class Tree {
  abstract void emitAsm(ref AsmFile);
}

class Statement : Tree { }

class Expr : Statement {
  abstract Type valueType();
}

class StringExpr : Expr {
  string str;
  // default action: place in string segment, load address on stack
  override void emitAsm(ref AsmFile af) {
    auto name = Format("cons_", af.constants.length);
    af.constants[name] = cast(ubyte[]) str;
    af.loadStack("$"~name);
  }
  override Type valueType() { return Type.CharPtr; }
}

bool gotStringExpr(ref string text, out Expr ex) {
  auto t2 = text;
  StringExpr se;
  return t2.accept("\"") &&
    (se = new StringExpr, true) &&
    (se.str = t2.slice("\""), true) &&
    (text = t2, true) &&
    (ex = se, true);
}

void callFunction(Function fun, Expr[] params, ref AsmFile dest) {
  assert(params.length == 0 /or/ 1, "TODO: basics");
  // ripped off from gcc hello world
  dest.put("pushl %ebp");
  dest.put("movl %esp, %ebp");
  assert(!params.length || params[0].valueType() == fun.paramType[0]);
  if (params.length) {
    // dest.put("andl $-16, %esp");
    // dest.put("subl $16, %esp");
    dest.put("subl $4, %esp");
    // TODO type conversion
    assert(fun.paramType.length == 1);
    assert(fun.retType == Type.Void);
    params[0].emitAsm(dest);
  }
  dest.put("call "~fun.name);
  dest.put("leave");
}

class Function : Tree {
  string name;
  Type retType;
  Type[] paramType;
  Statement _body;
  override void emitAsm(ref AsmFile af) {
    af.put(".globl "~name);
    af.put(".type "~name~", @function");
    af.put(name~": ");
    _body.emitAsm(af);
    af.put("ret");
  }
}

class Module : Tree {
  string name;
  Function[] funs;
  override void emitAsm(ref AsmFile af) {
    foreach (fun; funs) fun.emitAsm(af);
  }
}

bool gotModule(ref string text, out Module mod) {
  auto t2 = text;
  Function fp;
  return t2.accept("module ") && (mod = new Module, true) &&
    t2.gotIdentifier(mod.name) && t2.accept(";") &&
    many(t2.gotFunDef(fp), { mod.funs ~= fp; }) &&
    (text = t2, true);
}

bool bjoin(lazy bool c1, lazy bool c2, void delegate() dg) {
  if (!c1) return true;
  dg();
  while (true) {
    if (!c2) return true;
    if (!c1) return false;
    dg();
  }
}

// while expr
bool many(lazy bool b, void delegate() dg) {
  while (b()) dg();
  return true;
}

Function[string] fundb;

static this() {
  auto puts = new Function;
  puts.retType = Type.Void;
  puts.paramType ~= Type.CharPtr;
  puts.name = "puts";
  fundb["puts"] = puts;
}

Function lookup(string s) {
  assert(s in fundb, "Unknown function: "~s);
  return fundb[s];
}

class FunCall : Expr {
  string name;
  Expr[] params;
  override void emitAsm(ref AsmFile af) {
    callFunction(lookup(name), params, af);
  }
  override Type valueType() {
    return lookup(name).retType;
  }
}

bool gotIdentifier(ref string text, out string ident) {
  auto t2 = text.strip();
  if (!t2.length || !isAlphanum(t2[0])) return false;
  do {
    ident ~= t2.take();
  } while (t2.length && isAlphanum(t2[0]));
  text = t2;
  return true;
}

bool gotFuncall(ref string text, out Expr expr) {
  auto fc = new FunCall;
  string t2 = text;
  Expr ex;
  return t2.gotIdentifier(fc.name)
    && t2.accept("(")
    && bjoin(t2.gotExpr(ex), t2.accept(","), { fc.params ~= ex; })
    && t2.accept(")") && t2.accept(";")
    && ((text = t2), (expr = fc), true);
}

bool gotExpr(ref string text, out Expr expr) {
  return text.gotFuncall(expr) || text.gotStringExpr(expr);
}

class AggrStatement : Statement {
  Statement[] stmts;
  override void emitAsm(ref AsmFile af) {
    foreach (stmt; stmts)
      stmt.emitAsm(af);
  }
}

bool gotAggregateStmt(ref string text, out AggrStatement as) {
  auto t2 = text;
  
  Statement st;
  return t2.accept("{") && (as = new AggrStatement, true) &&
    many(t2.gotStatement(st), { if (!st) asm { int 3; } as.stmts ~= st; }) &&
    t2.accept("}") && (text = t2, true);
}

bool gotStatement(ref string text, out Statement stmt) {
  Expr ex;
  AggrStatement as;
  return
    (text.gotExpr(ex) && (stmt = ex, true)) ||
    (text.gotAggregateStmt(as) && (stmt = as, true));
}

bool gotFunDef(ref string text, out Function fun) {
  Type ptype;
  string t2 = text;
  fun = new Function;
  return t2.gotType(fun.retType)
    && t2.gotIdentifier(fun.name)
    && t2.accept("(")
    && bjoin(t2.gotType(ptype), t2.accept(","), {
      fun.paramType ~= ptype;
    }) && t2.accept(")") && t2.gotStatement(fun._body)
    && ((text = t2), (fundb[fun.name] = fun), true);
}

string compile(string file, bool saveTemps = false) {
  auto srcname = tmpnam("fcc_src"), objname = tmpnam("fcc_obj");
  scope(success) {
    if (!saveTemps)
      unlink(srcname.toStringz());
  }
  auto text = file.read().castLike("");
  Module mod;
  if (!text.gotModule(mod)) assert(false, "unable to eat module from "~file);
  if (text.strip().length) assert(false, "this text confuses me: "~text);
  AsmFile af;
  mod.emitAsm(af);
  srcname.write(af.genAsm());
  auto cmdline = Format("as -o ", objname, " ", srcname);
  writefln("> ", cmdline);
  system(cmdline.toStringz()) == 0 || assert(false);
  return objname;
}

void link(string[] objects, string output, string[] largs) {
  scope(success)
    foreach (obj; objects)
      unlink(obj.toStringz());
  string cmdline = "gcc -o "~output~" ";
  foreach (obj; objects) cmdline ~= obj ~ " ";
  foreach (larg; largs) cmdline ~= larg ~ " ";
  writefln("> ", cmdline);
  system(cmdline.toStringz());
}

void main(string[] args) {
  auto exec = args.take();
  string[] objects;
  string output;
  auto ar = args;
  string[] largs;
  bool saveTemps;
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
    if (arg == "-save-temps") {
      saveTemps = true;
      continue;
    }
    if (auto base = arg.endsWith(".cr")) {
      if (!output) output = arg[0 .. $-3];
      objects ~= arg.compile(saveTemps);
      continue;
    }
    return logln("Invalid argument: ", arg);
  }
  if (!output) output = "exec";
  objects.link(output, largs);
}
