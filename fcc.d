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

/*void main() {
  puts("Hello World");
}*/

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
  void[][string] constants;
  string code;
  void loadStack(string addr) {
    code ~= Format("movl "~addr~", (%esp)");
  }
  void put(T...)(T t) {
    code ~= Format(t, "\n");
  }
}

struct Tree {
  const Type = 0;
  int type;
  // default action
  void function(ref AsmFile) emitAsm;
}

struct Expr {
  const Type = 2;
  Tree tree;
  Type valueType;
}

struct StringExpr {
  const Type = 3;
  Expr expr;
  string str;
  // default action: place in string segment, load address on stack
  void genAsm(ref AsmFile af) {
    auto name = Format("Cons"~af.constants.length);
    af.constants[name] = str;
    af.loadStack(name);
  }
  StringExpr genStringExpr() {
    StringExpr res;
    res.expr.tree.emitAsm = &genAsm;
    res.expr.tree.type = Type;
    res.valueType = Type.CharPtr;
    return res;
  }
}

void callFunction(Function* fun, Expr*[] params, ref AsmFile dest) {
  assert(params.length == 1, "TODO: basics");
  // ripped off from gcc hello world
  dest.put("pushl %ebp");
  dest.put("movl %esp, %ebp");
  dest.put("andl $-16, %esp");
  dest.put("subl $16, %esp");
  // TODO type conversion
  assert(fun.paramType.length == 1);
  assert(params[0].tree.type == fun.paramType[0]);
  assert(fun.retType == Type.Void);
  params[0].tree.emitAsm(dest);
  dest.put("call "~fun.name);
}

struct Function {
  const Type = 1;
  Tree tree;
  string name;
  Type retType;
  Type[] paramType;
  Statement Body;
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

bool gotIdentifier(ref string text, out string ident) {
  if (!text.length || !isAlphanum(text[0])) return false;
  do {
    ident ~= text.take();
  } while (text.length && isAlphanum(text[0]));
  return true;
}

bool gotStatement(ref string text, out Statement stmt) {
  
}

bool gotFunDef(ref string text, out Function fun) {
  Type ptype; string ident;
  string t2 = text;
  return t2.gotType(fun.retType)
    && t2.gotIdentifier(fun.name)
    && t2.accept("(")
    && bjoin(t2.gotType(ptype), t2.accept(","), {
      fun.paramType ~= ptype;
    }) && t2.accept(")") && t2.gotStatement(fun.Body)
    && ((text = t2), true);
}

string compile(string file) {
  auto srcname = tmpnam("fcc_src"), objname = tmpnam("fcc_obj");
  scope(exit) {
    unlink(srcname.toStringz());
    // TODO move to linker when actually linkable
    unlink(objname.toStringz());
  }
  auto fe = new FileEntity;
  fe.text = file.read().castLike("");
  fe.filename = file;
  {
    Entity ent = new Root(fe);
    applyPass(ent, "section-file");
    applyPass(ent, "config-section");
    fe = cast(typeof(fe)) (cast(Root) ent).child;
  }
  logln("Product: ", fe);
  // srcname.write(fe.generate()); // TODO: actually compile  
  return null;
}

void main(string[] args) {
  auto exec = args.take();
  string[] objects;
  string output;
  auto ar = args;
  string[] largs;
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
    if (auto base = arg.endsWith(".cr")) {
      if (!output) output = arg[0 .. $-3];
      objects ~= arg.compile();
      continue;
    }
    return logln("Invalid argument: ", arg);
  }
  if (!output) output = "exec";
  logln("Skip linking");
  // objects.link(output, largs);
}
