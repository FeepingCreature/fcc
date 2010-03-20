module fcc; // feep's crazed compiler

import tools.base, tools.log, tools.compat;

extern(C) {
  int mkstemp(char* tmpl);
  int close(int fd);
}

string error;

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

string next_text(string s) {
  if (s.length > 100) s = s[0 .. 100];
  return s.replace("\n", "\\");
}

bool accept(ref string s, string t) {
  auto s2 = s.strip();
  t = t.strip();
  // logln("accept ", t, " from ", s2.next_text(), "? ", !!s2.startsWith(t));
  return s2.startsWith(t) && (s = s2[t.length .. $], true);
}

/+
  What do we expect of a type system?
  Nothing.
+/

class Type {
  int size;
  int opEquals(Object obj) {
    // specialize where needed
    return this.classinfo is obj.classinfo &&
      size == (cast(Type) cast(void*) obj).size;
  }
  void match(ref Expr[] params) {
    if (!params.length)
      throw new Exception(Format("Missing parameter of ", this));
    if (params[0].valueType() !is this)
      throw new Exception(Format("Expected ", this, ", got ", params[0]));
    params.take();
  }
}

class Void : Type {
  this() { size = 4; }
}

class Variadic : Type {
  this() { size = 0; }
  void match(ref Expr[] params) {
    params = null; // match all
  }
}

class Char : Type {
  this() { size = 1; }
}

const nativeIntSize = 4, nativePtrSize = 4;

class SizeT : Type {
  this() { size = nativeIntSize; }
}

class SysInt : Type {
  this() { size = nativeIntSize; }
}

class Pointer : Type {
  Type target;
  this(Type t) { target = t; size = nativePtrSize; }
  int opEquals(Object obj) {
    if (obj.classinfo !is this.classinfo) return false;
    auto p = cast(Pointer) cast(void*) obj;
    return target == p.target;
  }
}

Type[] type_memofield;

// TODO: memoize better
Type tmemo(Type t) {
  foreach (entry; type_memofield) {
    if (entry.classinfo is t.classinfo && entry == t) return entry;
  }
  type_memofield ~= t;
  return t;
}

class ParseException {
  string where, info;
  this(string where, string info) {
    this.where = where; this.info = info;
  }
}

bool gotType(ref string text, out Type type) {
  if (text.accept("void")) return type = tmemo(new Void), true;
  if (text.accept("size_t")) return type = tmemo(new SizeT), true;
  if (text.accept("int")) return type = tmemo(new SysInt), true;
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
  override Type valueType() { return tmemo(new Pointer(new Char)); }
}

bool gotStringExpr(ref string text, out Expr ex) {
  auto t2 = text;
  StringExpr se;
  return t2.accept("\"") &&
    (se = new StringExpr, true) &&
    (se.str = t2.slice("\"").replace("\\n", "\n"), true) &&
    (text = t2, true) &&
    (ex = se, true);
}

class IntExpr : Expr {
  int num;
  override void emitAsm(ref AsmFile af) {
    af.loadStack(Format("$", num));
  }
  override Type valueType() { return tmemo(new SysInt); }
  this(int i) { num = i; }
}

bool gotIntExpr(ref string text, out Expr ex) {
  auto t2 = text.strip();
  if (auto rest = t2.startsWith("-")) {
    return gotIntExpr(rest, ex)
      && (
        ((cast(IntExpr) ex).num = -(cast(IntExpr) ex).num),
        (text = rest),
        true
      );
    }
  bool isNum(char c) { return c >= '0' && c <= '9'; }
  if (!t2.length || !isNum(t2[0])) return false;
  int res = t2.take() - '0';
  while (t2.length) {
    if (!isNum(t2[0])) break;
    res = res * 10 + t2.take() - '0'; 
  }
  ex = new IntExpr(res);
  text = t2;
  return true;
}

void callFunction(Function fun, Expr[] params, ref AsmFile dest) {
  // dest.put("int $3");
  if (params.length) {
    auto p2 = params;
    foreach (entry; fun.params)
      entry._0.match(p2);
    assert(!p2.length);
    assert(cast(Void) fun.retType);
    foreach_reverse (param; params) {
      dest.put(Format("subl $", param.valueType().size, ", %esp"));
      param.emitAsm(dest);
    }
  } else assert(!fun.params.length, Format("Expected ", fun.params, "!"));
  dest.put("call "~fun.name);
  foreach (param; params) {
    dest.put(Format("addl $", param.valueType().size, ", %esp"));
  }
  // dest.put("leave");
}

// information about active stack frame
// built while generating function
class FrameState {
  Variable[] vars;
  string toString() {
    return Format(
      super.toString(), " - ", size(), " in ", vars
    );
  }
  int size() {
    int res;
    // TODO: alignment
    foreach (var; vars)
      res += var.type.size;
    return res;
  }
}

class Function : Tree {
  string name;
  Type retType;
  Stuple!(Type, string)[] params;
  FrameState frame;
  Statement _body;
  // declare parameters as variables
  void fixup() {
    // cdecl: 0 old ebp, 4 return address, 8 parameters .. I think.
    int cur = 8;
    // TODO: alignment
    foreach (param; params) {
      if (param._1) frame.vars ~= new Variable(param._0, param._1, cur);
      cur += param._0.size;
    }
  }
  override void emitAsm(ref AsmFile af) {
    af.put(".globl "~name);
    af.put(".type "~name~", @function");
    af.put(name~": ");
    af.put("pushl %ebp");
    af.put("movl %esp, %ebp");
    // af.put("subl $", frame.size, ", %esp");
    _body.emitAsm(af);
    af.put("movl %ebp, %esp");
    af.put("popl %ebp");
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
  puts.retType = tmemo(new Void);
  puts.params ~= stuple(tmemo(new Pointer(new Char)), cast(string) null);
  puts.name = "puts";
  fundb["puts"] = puts;
  auto printf = new Function;
  printf.retType = tmemo(new Void);
  printf.params ~= stuple(tmemo(new Pointer(new Char)), cast(string) null);
  printf.params ~= stuple(tmemo(new Variadic), cast(string) null);
  printf.name = "printf";
  fundb["printf"] = printf;
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

bool gotFuncall(ref string text, out Expr expr, FrameState fs) {
  auto fc = new FunCall;
  string t2 = text;
  Expr ex;
  return t2.gotIdentifier(fc.name)
    && t2.accept("(")
    && bjoin(t2.gotExpr(ex, fs), t2.accept(","), { fc.params ~= ex; })
    && t2.accept(")")
    && ((text = t2), (expr = fc), true);
}

bool gotVariable(ref string text, out Variable v, FrameState fs) {
  // logln("Match variable off ", text.next_text());
  Variable var;
  string name, t2 = text;
  return t2.gotIdentifier(name)
    && {
      // logln("Look for ", name, " in ", fs.vars);
      foreach (var; fs.vars)
        if (var.name == name) {
          v = var;
          text = t2;
          return true;
        }
      error = "unknown identifier "~name;
      return false;
    }();
}

bool gotExpr(ref string text, out Expr expr, FrameState fs) {
  Variable var;
  return
       text.gotFuncall(expr, fs)
    || text.gotStringExpr(expr)
    || text.gotIntExpr(expr)
    || text.gotVariable(var, fs) && (expr = var, true);
}

class AggrStatement : Statement {
  Statement[] stmts;
  override void emitAsm(ref AsmFile af) {
    foreach (stmt; stmts)
      stmt.emitAsm(af);
  }
}

bool gotAggregateStmt(ref string text, out AggrStatement as, FrameState fs) {
  auto t2 = text;
  
  Statement st;
  return t2.accept("{") && (as = new AggrStatement, true) &&
    many(t2.gotStatement(st, fs), { if (!st) asm { int 3; } as.stmts ~= st; }) &&
    t2.accept("}") && (text = t2, true);
}

class Assignment : Statement {
  Variable target;
  Expr value;
  this(Variable v, Expr e) { target = v; value = e; }
  this() { }
  override void emitAsm(ref AsmFile af) {
    assert(value.valueType().size == 4);
    value.emitAsm(af);
    af.put(Format("movl (%esp), %edx"));
    af.put(Format("movl %edx, ", target.baseOffset, "(%ebp)"));
    af.put(Format("addl $4, %esp"));
  }
}

bool gotAssignment(ref string text, out Assignment as, FrameState fs) {
  auto t2 = text;
  New(as);
  return t2.gotVariable(as.target, fs) && t2.accept("=") && t2.gotExpr(as.value, fs) && t2.accept(";") && {
    text = t2;
    return true;
  }();
}

class Variable : Expr {
  override void emitAsm(ref AsmFile af) {
    assert(type.size == 4);
    af.put(Format("movl ", baseOffset, "(%ebp), %edx"));
    af.put(Format("movl %edx, (%esp)"));
    if (initAss) initAss.emitAsm(af);
  }
  override Type valueType() {
    return type;
  }
  Type type;
  string name;
  // offset off ebp
  int baseOffset;
  Assignment initAss;
  this(Type t, string s, int i) { type = t; name = s; baseOffset = i; }
  this() { }
  string toString() { return Format("[ var ", name, " of ", type, " at ", baseOffset, "]"); }
}

class VarDecl : Statement {
  override void emitAsm(ref AsmFile af) {
    af.put("subl $4, %esp");
  }
  Variable var;
}

bool gotVarDecl(ref string text, out VarDecl vd, FrameState fs) {
  auto t2 = text;
  auto var = new Variable;
  Expr testInit;
  return
    t2.gotType(var.type)
    && t2.gotIdentifier(var.name)
    && (t2.accept("=") && t2.gotExpr(testInit, fs) && {
      var.initAss = new Assignment(var, testInit);
      return true;
    }() || true)
    && t2.accept(";")
    && {
      var.baseOffset = -fs.size; // TODO: check
      New(vd);
      vd.var = var;
      fs.vars ~= var;
      text = t2;
      return true;
    }();
}

bool gotStatement(ref string text, out Statement stmt, FrameState fs) {
  // logln("match statement from ", text.next_text());
  Expr ex;
  AggrStatement as;
  VarDecl vd;
  Assignment ass;
  auto t2 = text;
  return
    (t2.gotExpr(ex, fs) && t2.accept(";") && (text = t2, stmt = ex, true)) ||
    (text.gotVarDecl(vd, fs) && (stmt = vd, true)) ||
    (text.gotAggregateStmt(as, fs) && (stmt = as, true)) ||
    (text.gotAssignment(ass, fs) && (stmt = ass, true));
}

bool gotFunDef(ref string text, out Function fun) {
  Type ptype;
  string t2 = text;
  fun = new Function;
  fun.frame = new FrameState;
  // scope(exit) logln("frame state ", fun.frame);
  string parname;
  return t2.gotType(fun.retType)
    && t2.gotIdentifier(fun.name)
    && t2.accept("(")
    // TODO: function parameters belong on the stackframe
    && bjoin(t2.gotType(ptype) && (t2.gotIdentifier(parname) || ((parname=null), true)), t2.accept(","), {
      fun.params ~= stuple(ptype, parname);
    }) && t2.accept(")") && (fun.fixup, true) && t2.gotStatement(fun._body, fun.frame)
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
  if (!text.gotModule(mod)) assert(false, "unable to eat module from "~file~": "~error);
  if (text.strip().length) assert(false, "this text confuses me: "~text~": "~error);
  AsmFile af;
  mod.emitAsm(af);
  srcname.write(af.genAsm());
  auto cmdline = Format("as -o ", objname, " ", srcname);
  writefln("> ", cmdline);
  system(cmdline.toStringz()) == 0
    || assert(false, "Compilation failed! ");
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
    if (arg == "-save-temps" || arg == "-S") {
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
