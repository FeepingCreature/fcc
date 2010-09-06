module ast.base;

public import asmfile, ast.types, parseBase, tools.log: logln;

import tools.base: Format, New;

interface Iterable {
  void iterate(void delegate(ref Iterable) dg);
  Iterable dup();
}

interface Tree : Iterable {
  void emitAsm(AsmFile);
  Tree dup();
}

interface NeedsConfig {
  // must be called after the expression has been selected for sure
  // used to set up temporary variables
  void configure();
}

void configure(Iterable it) {
  void fun(ref Iterable it) {
    if (auto nc = cast(NeedsConfig) it)
      nc.configure();
    else it.iterate(&fun);
  }
  fun(it);
}

template MyThis(string S) {
  mixin(This_fn(rmSpace!(S)));
  private this() { }
}

template DefaultDup() {
  override typeof(this) dup() {
    auto res = new typeof(this);
    foreach (i, v; this.tupleof) {
      static if (is(typeof(v[0].dup))) {
        res.tupleof[i] = new typeof(v[0])[this.tupleof[i].length];
        foreach (k, ref entry; res.tupleof[i])
          entry = this.tupleof[i][k].dup;
      } else static if (is(typeof(v.dup))) {
        if (this.tupleof[i])
          res.tupleof[i] = this.tupleof[i].dup;
      } else {
        res.tupleof[i] = this.tupleof[i];
      }
    }
    return res;
  }
}

import tools.ctfe;
string genIterates(int params) {
  if (params < 0) return null;
  string res = "template defaultIterate(";
  for (int i = 0; i < params; ++i) {
    if (i) res ~= ", ";
    res ~= "alias A"~ctToString(i);
  }
  res ~= ") {
    override void iterate(void delegate(ref Iterable) dg) {";
  for (int i = 0; i < params; ++i) {
    res ~= `
      {
        static if (is(typeof({ foreach (i, ref entry; $A) {} }))) {
          foreach (i, ref entry; $A) {
            Iterable iter = entry;
            if (!iter) continue;
            dg(iter);
            if (iter !is entry) {
              auto res = cast(typeof(entry)) iter;
              if (!res) throw new Exception(Format("Cannot substitute ", $A, "[", i, "] with ", res, ": ", typeof(entry).stringof, " expected! "));
              entry = res;
            }
          }
        } else {
          if (Iterable iter = $A) {
            dg(iter);
            if (iter !is $A) {
              auto res = cast(typeof($A)) iter;
              if (!res) throw new Exception(Format("Cannot substitute ", $A, " with ", res, ": ", typeof($A).stringof, " expected! "));
              $A = res;
            }
          }
        }
      }`.ctReplace("$A", "A"~ctToString(i));
  }
  res ~= "
    }
  }
  ";
  return res ~ genIterates(params - 1);
}

mixin(genIterates(9));

interface Named {
  string getIdentifier();
}

interface SelfAdding { // may add themselves to the respective namespace
  bool addsSelf();
}

bool addsSelf(T)(T t) { auto sa = cast(SelfAdding) t; return sa && sa.addsSelf(); }

interface Statement : Tree {
  override Statement dup();
}

interface Literal {
  string getValue(); // as assembler literal
}

class NoOp : Statement {
  NoOp dup() { return this; }
  override void emitAsm(AsmFile af) { }
  mixin defaultIterate!();
}

interface Expr : Tree {
  IType valueType();
  override Expr dup();
}

// has a pointer, but please don't modify it - ie. string literals
interface CValue : Expr {
  void emitLocation(AsmFile);
  override CValue dup();
}

// free to modify
interface LValue : CValue {
  override LValue dup();
}

// more than rvalue, less than lvalue
interface MValue : Expr {
  void emitAssignment(AsmFile); // eat value from stack and store
  override MValue dup();
}

// used as assignment source placeholder in emitAssignment
class Placeholder : Expr {
  IType type;
  mixin defaultIterate!();
  this(IType type) { this.type = type; }
  override IType valueType() { return type; }
  override void emitAsm(AsmFile af) { }
  private this() { }
  mixin DefaultDup!();
}

// can be printed as string
interface Formatable {
  Expr format(Expr ex);
}

/// Emitting this sets up FLAGS.
/// TODO: how does this work on non-x86?
interface Cond : Iterable {
  void jumpOn(AsmFile af, bool cond, string dest);
  override Cond dup();
}

interface IRegister {
  string getReg();
}

class Register(string Reg) : Expr, IRegister {
  override string getReg() { return Reg; }
  mixin defaultIterate!();
  override IType valueType() { return Single!(SysInt); }
  override void emitAsm(AsmFile af) {
    af.pushStack("%"~Reg, valueType());
  }
  override Register dup() { return this; }
}

string error; // TODO: tls

class ParseException {
  string where, info;
  this(string where, string info) {
    this.where = where; this.info = info;
  }
}

ulong uid;
ulong getuid() { synchronized return uid++; }

void withTLS(T, U, V)(T obj, U value, lazy V vee) {
  auto backup = obj();
  scope(exit) obj.set(backup);
  obj.set(value);
  static if (is(typeof(vee()()))) vee()();
  else static if (is(typeof(vee()))) vee();
  else static assert(false, "Can't call "~V.stringof);
}

/// can be transformed into an obj relative to a base
interface RelTransformable {
  Object transform(Expr base);
}

// ctfe
string mustOffset(string value) {
  
  string hash;
  foreach (ch; value)
    if (ch >= '0' && ch <= '9' || ch >= 'a' && ch <= 'z' || ch >= 'A' && ch <= 'Z')
      hash ~= ch;
  if (hash.length) hash = "__start_offs_"~hash;
  else hash = "__start_offs";
  
  return (`
    auto OFFS = af.currentStackDepth;
    scope(success) assert(af.currentStackDepth == OFFS + `~value~`,
      Format("Stack offset violated: got ", af.currentStackDepth, "; expected ", OFFS, " + ", `~value~`)
    );`).ctReplace("\n", "", "OFFS", hash); // fix up line numbers!
}

class CallbackExpr : Expr {
  IType type;
  void delegate(AsmFile) dg;
  this(IType type, void delegate(AsmFile) dg) {
    this.type = type; this.dg = dg;
  }
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { dg(af); }
    mixin defaultIterate!(); // TODO
  }
  private this() { }
  mixin DefaultDup!();
}

interface ScopeLike {
  int framesize();
}

Expr delegate(Expr)[] foldopt; // a thing that flattens
