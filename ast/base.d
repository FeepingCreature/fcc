module ast.base;

public import asmfile, ast.types, parseBase, errors, tools.log: logln;

import tools.base: Format, New, This_fn, rmSpace;

interface Iterable {
  void iterate(void delegate(ref Iterable) dg);
  Iterable dup();
}

interface Tree : Iterable {
  void emitAsm(AsmFile);
  Tree dup();
}

interface Setupable {
  void setup(AsmFile); // register globals and such
}
void delegate(Setupable) registerSetupable;

interface NeedsConfig {
  // must be called after the expression has been selected for sure
  // used to set up temporary variables
  void configure();
}

interface IsMangled { string mangleSelf(); }

void delegate(IsMangled) addExtra;

interface FrameRoot { int framestart(); } // Function

// pointer for structs, ref for classes
interface hasRefType {
  IType getRefType();
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

void checkType(Iterable it, void delegate(ref Iterable) dg) {
  if (auto ex = cast(Expr) it) {
    if (auto it = cast(Iterable) ex.valueType()) {
      it.iterate(dg);
    }
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
            // checkType(iter, dg);
            if (iter !is entry) {
              auto res = cast(typeof(entry)) iter;
              if (!res) throw new Exception(Format("Cannot substitute ", $A, "[", i, "] with ", res, ": ", typeof(entry).stringof, " expected! "));
              entry = res;
            }
          }
        } else {
          if (Iterable iter = $A) {
            dg(iter);
            // checkType(iter, dg);
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

interface HasInfo {
  string getInfo();
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
string mustOffset(string value, string _hash = null) {
  
  string hash = _hash;
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

private alias Iterable Itr;

Itr delegate(Itr)[] _foldopt; // a thing that flattens

struct foldopt {
  static {
    void opCatAssign(Itr delegate(Itr) dg) {
      _foldopt ~= dg;
    }
    void opCatAssign(Expr delegate(Expr) dg) {
      _foldopt ~= dg /apply/ delegate Itr(typeof(dg) dg, Itr it) {
        auto ex = cast(Expr) it;
        if (!ex) return null;
        auto res = dg(ex);
        return cast(Itr) res;
      };
    }
    int opApply(int delegate(ref Itr delegate(Itr)) dg) {
      foreach (dg2; _foldopt)
        if (auto res = dg(dg2)) return res;
      return 0;
    }
  }
}

class StatementAndExpr : Expr {
  Statement first;
  Expr second;
  mixin MyThis!("first, second");
  mixin defaultIterate!(first, second);
  bool once;
  override {
    string toString() { return Format("sae{", first, second, "}"); }
    StatementAndExpr dup() {
      return new StatementAndExpr(first.dup, second.dup);
    }
    IType valueType() { return second.valueType(); }
    void emitAsm(AsmFile af) {
      if (once) {
        logln("Double emit S&E. NOT SAFE. Expr is ", second, "; statement is ", first);
        asm { int 3; }
      }
      once = true;
      first.emitAsm(af);
      second.emitAsm(af);
    }
  }
}

class PlaceholderToken : Expr {
  IType type;
  string info;
  this(IType type, string info) { this.type = type; this.info = info; }
  PlaceholderToken dup() { return this; } // IMPORTANT.
  mixin defaultIterate!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { logln("DIAF ", info); asm { int 3; } assert(false); }
    string toString() { return Format("Placeholder(", info, ")"); }
  }
}

class PlaceholderTokenLV : PlaceholderToken, LValue {
  PlaceholderTokenLV dup() { return this; }
  this(IType type, string info) { super(type, info); }
  override void emitLocation(AsmFile af) { assert(false); }
}
