module ast.base;

public import asmfile, ast.types, parseBase, errors, tools.log: logln;

public import casts;

import tools.base: Format, New, This_fn, rmSpace;

const string EXT = ".nt";

string platform_prefix;

bool isWindoze() {
  return platform_prefix.find("mingw") != -1;
}

string[] extra_linker_args;

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

// used to suppress struct method auto-emit if inside a struct template
interface HandlesEmits {
  bool handledEmit(Tree tr);
}

interface IsMangled { string mangleSelf(); void markWeak(); }

interface FrameRoot { int framestart(); } // Function

// pointer for structs, ref for classes
interface hasRefType {
  IType getRefType();
}

void configure(Iterable it) {
  void fun(ref Iterable it) {
    if (auto nc = fastcast!(NeedsConfig)(it))
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
  if (auto ex = fastcast!(Expr)~ it) {
    if (auto it = fastcast!(Iterable)~ ex.valueType()) {
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
              auto res = fastcast!(typeof(entry)) (iter);
              if (!res) throw new Exception(Format("Cannot substitute ", $A, "[", i, "] with ", iter, " of ", (fastcast!(Object) (iter)).classinfo.name, ": ", typeof(entry).stringof, " expected! "));
              entry = res;
            }
          }
        } else {
          Iterable iter;
          static if (is($A: Iterable)) iter = $A;
          else iter = fastcast!(Iterable) ($A);
          if (iter) {
            dg(iter);
            // checkType(iter, dg);
            if (iter !is $A) {
              auto res = fastcast!(typeof($A)) (iter);
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

bool addsSelf(T)(T t) { auto sa = fastcast!(SelfAdding) (t); return sa && sa.addsSelf(); }

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

class Filler : Expr {
  IType type;
  this(IType type) { this.type = type; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { af.salloc(type.size); }
  }
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
    af.pushStack("%"~Reg, 4);
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
    scope(success) if (af.currentStackDepth != OFFS + `~value~`) {
      logln("Stack offset violated: got ", af.currentStackDepth, "; expected ", OFFS, " + ", `~value~`);
      fail();
    }`).ctReplace("\n", "", "OFFS", hash); // fix up line numbers!
}

class CallbackExpr : Expr {
  IType type;
  Expr ex; // held for dg so it can iterate properly
  void delegate(Expr, AsmFile) dg;
  this(IType type, Expr ex, void delegate(Expr, AsmFile) dg) {
    this.type = type; this.ex = ex; this.dg = dg;
  }
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { dg(ex, af); }
    mixin defaultIterate!(ex);
  }
  private this() { }
  mixin DefaultDup!();
}

interface ScopeLike {
  int framesize();
  Statement[] getGuards();
}

private alias Iterable Itr;

Itr delegate(Itr)[] _foldopt; // a thing that flattens

struct foldopt {
  static {
    void opCatAssign(Itr delegate(Itr) dg) {
      _foldopt ~= dg;
    }
    int opApply(int delegate(ref Itr delegate(Itr)) dg) {
      foreach (dg2; _foldopt)
        if (auto res = dg(dg2)) return res;
      return 0;
    }
  }
}

template StatementAndT(T) {
  class StatementAndT : T {
    static if (is(T == Expr)) const string NAME = "sae";
    static if (is(T == LValue)) const string NAME = "sal";
    static if (is(T == MValue)) const string NAME = "sam"; // Seriously?
    Statement first;
    T second;
    bool permissive;
    mixin MyThis!("first, second, permissive = false");
    mixin defaultIterate!(first, second);
    bool once;
    bool check() {
      if (once) {
        if (permissive) return false;
        logln("Double emit ", this, ". NOT SAFE. ");
        asm { int 3; }
      }
      once = true;
      return true;
    }
    override {
      string toString() { return Format(NAME, "{", first, second, "}"); }
      StatementAndT dup() { return new StatementAndT(first.dup, second.dup); }
      IType valueType() { return second.valueType(); }
      void emitAsm(AsmFile af) {
        if (check) first.emitAsm(af);
        second.emitAsm(af);
      }
      static if (is(T: LValue)) void emitLocation(AsmFile af) {
        if (check) first.emitAsm(af);
        second.emitLocation(af);
      }
      static if (is(T: MValue)) void emitAssignment(AsmFile af) {
        if (check) first.emitAsm(af);
        second.emitAssignment(af);
      }
    }
  }
}

alias StatementAndT!(Expr) StatementAndExpr;
alias StatementAndT!(LValue) StatementAndLValue;
alias StatementAndT!(MValue) StatementAndMValue;

Expr mkStatementAndExpr(Statement st, Expr ex, bool permissive = false) {
  if (auto mv = fastcast!(MValue) (ex))
    return new StatementAndMValue(st, mv, permissive);
  if (auto lv = fastcast!(LValue) (ex))
    return new StatementAndLValue(st, lv, permissive);
  return new StatementAndExpr(st, ex, permissive);
}

class PlaceholderToken : Expr {
  IType type;
  string info;
  this(IType type, string info) { this.type = type; this.info = info; }
  PlaceholderToken dup() { return this; } // IMPORTANT.
  mixin defaultIterate!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { logln("DIAF ", info, " of ", type); asm { int 3; } assert(false); }
    string toString() { return Format("Placeholder(", info, ")"); }
  }
}

class PlaceholderTokenLV : PlaceholderToken, LValue {
  PlaceholderTokenLV dup() { return this; }
  this(IType type, string info) { super(type, info); }
  override void emitLocation(AsmFile af) { assert(false); }
  override string toString() { return Format("PlaceholderLV(", info, ")"); }
}

string qbuffer;
int offs;

void qformat_append(T...)(T t) {
  void qbuffer_resize(int i) {
    if (qbuffer.length < i) {
      auto backup = qbuffer;
      qbuffer = new char[max(16384, i)];
      qbuffer[0 .. backup.length] = backup;
    }
  }
  void append(string s) {
    qbuffer_resize(offs + s.length);
    qbuffer[offs .. offs+s.length] = s;
    offs += s.length;
  }
  foreach (entry; t) {
    static if (is(typeof(entry): string)) {
      append(entry);
    }
    else static if (is(typeof(entry): ulong)) {
      auto num = entry;
      if (!num) { append("0"); continue; }
      if (num < 0) { append("-"); num = -num; }
      
      // gotta do this left to right!
      typeof(num) ifact = 1;
      while (ifact <= num / 10) ifact *= 10;
      while (ifact) {
        int inum = num / ifact;
        char[1] ch;
        ch[0] = "0123456789"[inum];
        append(ch);
        num -= cast(long) inum * cast(long) ifact;
        ifact /= 10L;
      }
    }
    else static if (is(typeof(entry[0]))) {
      append("[");
      bool first = true;
      foreach (element; entry) {
        if (first) first = false;
        else append(", ");
        qformat_append(element);
      }
      append("]");
    }
    else static if (is(typeof(fastcast!(Object) (entry)))) {
      auto obj = fastcast!(Object) (entry);
      append(obj.toString());
    }
    else static assert(false, "not supported in qformat: "~typeof(entry).stringof);
  }
}

string qformat(T...)(T t) {
  offs = 0;
  qformat_append(t);
  auto res = qbuffer[0 .. offs];
  qbuffer = qbuffer[offs .. $];
  return res;
}

interface ForceAlignment {
  int alignment(); // return 0 if don't need special alignment after all
}

extern(C) int align_boffs(IType t, int curdepth = -1);

int delegate(IType)[] alignChecks;

int roundTo(int i, int to) {
  auto i2 = (i / to) * to;
  if (i2 != i) return i2 + to;
  else return i;
}

int needsAlignment(IType it) {
  foreach (check; alignChecks)
    if (auto res = check(it)) return res;
  const limit = 4;
  it = resolveType(it);
  if (auto fa = fastcast!(ForceAlignment) (it))
    if (auto res = fa.alignment()) return res;
  if (it.size > limit) return limit;
  else return it.size;
}

void doAlign(ref int offset, IType type) {
  int to = needsAlignment(type);
  if (!to) return; // what. 
  offset = roundTo(offset, to);
}

int getFillerFor(IType t, int depth) {
  auto nd = -align_boffs(t, depth) - t.size;
  return nd - depth;
}

int alignStackFor(IType t, AsmFile af) {
  auto delta = getFillerFor(t, af.currentStackDepth);
  af.salloc(delta);
  return delta;
}

extern(C) {
  struct winsize {
    ushort row, col, xpixel, ypixel;
  }
  int ioctl(int d, int request, ...);
  void* stdin;
  int fflush(void* stream);
}
template logSmart(bool Mode) {
  void logSmart(T...)(T t) {
    tools.log.log("\r");
    auto pretext = Format(t);
    string text;
    foreach (ch; pretext) {
      if (ch == '\t') {
        while (text.length % 8 != 0) text ~= " ";
      } else text ~= ch;
    }
    winsize ws;
    ioctl(0, /*TIOCGWINSZ*/0x5413, &ws);
    string empty;
    for (int i = 0; i < ws.col - 1; ++i) empty ~= " ";
    tools.log.log("\r", empty, "\r");
    tools.log.log(text);
    if (Mode) tools.log.log("\r");
    else tools.log.log("\n");
    fflush(stdin);
  }
}

extern(C) void _line_numbered_statement_emitAsm(LineNumberedStatement, AsmFile);

interface LineNumberedStatement : Statement {
	LineNumberedStatement dup();
	void configPosition(string text);
	void getInfo(ref string name, ref int line);
}

class LineNumberedStatementClass : LineNumberedStatement {  
  int line;
  string name;
  abstract LineNumberedStatement dup();
  abstract void iterate(void delegate(ref Iterable) dg);
  override void getInfo(ref string n, ref int l) { n = name; l = line; }
  override void configPosition(string text) {   
    auto pos = lookupPos(text);
    line = pos._0 + 1;
    name = pos._2;
  }
  override void emitAsm(AsmFile af) {
    _line_numbered_statement_emitAsm(this, af);
  }
}

string mainfile;

import std.moduleinit;
void registerClass(string modname, Object obj) {
  foreach (globmod; ModuleInfo.modules) {
    if (globmod.name == modname)
      globmod.localClasses ~= obj.classinfo;
  }
}

static this() {
  registerClass("ast.base", new Register!("ebp"));
}

bool function(Expr) isTrivial;

// some exprs must immediately be replaced with others
// for instance, one-entry tuples
Expr delegate(Expr) forcedConversionDg;
Expr forcedConvert(Expr ex) {
  if (!forcedConversionDg) return ex;
  return forcedConversionDg(ex);
}

IType delegate(IType) forcedTypeConversionDg;
IType forcedConvert(IType it) {
  if (!forcedTypeConversionDg) return it;
  return forcedTypeConversionDg(it);
}

Object[string] internals; // parsed for in ast.intrinsic

TLS!(Stuple!(string, IType)) templInstOverride;
static this() { New(templInstOverride); }

TLS!(string) currentPropBase;
static this() { New(currentPropBase); }
