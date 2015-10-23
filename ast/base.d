module ast.base;

int xpar = -1; // for debugging. see xpar_bisect.nt

public import llvmfile, ast.types, parseBase, errors, tools.log: logln;

public import casts, alloc, quickformat;

import tools.base: fail, find, Format, New, This_fn, rmSpace, Stuple, slice, endsWith;
import tools.ctfe: ctReplace;
import std.c.stdio;

const string EXT = ".nt";

string path_prefix, platform_prefix;

bool doBreak;
void breakpoint() {
  if (doBreak) asm { int 3; }
}

const string tlsbase = "_threadlocal";

bool isWindoze() {
  return platform_prefix.find("mingw"[]) != -1;
}

bool isARM() {
  return !!platform_prefix.startsWith("arm"[]);
}

bool isX86() {
  return !isARM(); // lel
}

version(Windows) static this() { platform_prefix = "i686-mingw32-"; }

string[] extra_linker_args;

bool releaseMode;

enum IterMode { Lexical, Semantic }

interface Iterable {
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical);
  Iterable dup();
}

interface Tree : Iterable {
  void emitLLVM(LLVMFile);
  Tree dup();
  // returns a version that is semantically identical (emits the same LLVM code)
  // but structurally simplified.
  /// Why not collapse everything from the start?
  // Sometimes there's semantic information that's required for parsing
  // but not code generation, such as tuple labels.
  /// Why not use foldex/opt?
  // This is faster. Basically, it replaces every foldopt that starts with 
  // > auto thing = fastcast!(Thing)(it); if (!thing) return null;
  Tree collapse();
}

interface Setupable {
  void setup(LLVMFile); // register globals and such
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

interface IsMangled { string mangleSelf(); void markWeak(); void markExternC(); }

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

// used when there are multiple elements, of which we may prefer one
interface Scored {
  int getScore(); // smaller is better
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
    /*override*/ void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {";
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
              if (!res) {
                logln(this, "\n\n: cannot substitute ", $A, "\n\n[", i, "]with ", iter, " of ", (fastcast!(Object) (iter)).classinfo.name, ": ", typeof(entry).stringof, " expected! ");
                fail;
              }
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
              if (!res) {
                logln(this, ": cannot substitute ", $A);
                logln(" with ", iter, ": got ", fastcast!(Object)(iter).classinfo.name, ", expected ", typeof($A).stringof);
                fail;
              }
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

extern(C) Expr C_foldex(Expr, bool);
extern(C) bool is_unsafe_fast();

template defaultCollapse(T...) {
  static assert(!T.length);
  static if (is(typeof(this):Tree)) { alias Tree RetType; }
  else static if (is(typeof(this):Cond)) { alias Cond RetType; }
  else alias typeof(this) RetType;
  /*override*/ RetType collapse() {
    const debugmode = false;
    static if (debugmode && is(typeof(this): Expr)) {
      Expr nex = ast.base.C_foldex(this, false);
      if (nex !is fastcast!(Expr)(this)) {
        Expr ex = this;
        // D bughunting debris. See casts.d "cast(T) cast(Object) "
        /*logln(typeof(this).stringof);
        logln("test: ", cast(void*) ex, " ", cast(void*) this);
        logln("1: ", cast(void*) fastcast!(Expr)(fastcast!(Itr)(this)));
        logln("1: ", cast(void*) fastcast!(Expr)(this));
        logln("2: ", cast(void*) cast(Expr) cast(Itr) this);
        logln("2: ", cast(void*) cast(Expr) this);
        logln("3: ", cast(void*) cast(Expr) cast(Itr) cast(Object) this);
        logln("3: ", cast(void*) cast(Expr) cast(Object) this);
        logln("of course: ", typeof(this).stringof, " and ", this.classinfo.name, " and ", fastcast!(Object)(this).classinfo.name);*/
        logln("Move foldex into collapse in ", typeof(this).stringof, "!");
        logln("from: ", cast(void*)(fastcast!(Expr)~this), " ", this.classinfo.name, " ", this);
        logln("to  : ", cast(void*)(fastcast!(Expr)~nex), " ", (fastcast!(Object)(nex)).classinfo.name, " ", nex);
        Itr cur = this;
        while (true) {
          auto start = cur;
          foreach (dg; foldopt) {
            if (auto res = dg(cur)) {
              logln("modified by");
              asm { int 3; }
              dg(cur);
              cur = res;
            }
          }
          if (cur is start) break;
        }
        fail;
      }
    }
    return this;
  }
}

// caching not worth it (I tried)
Tree collapse(Tree t) {
retry:
  auto nt = t.collapse();
  if (t is nt) return t;
  // logln("from: ", t);
  // logln("to: ", nt);
  t = nt;
  goto retry;
}

Cond collapse(Cond cd) {
retry:
  auto nc = cd.collapse();
  if (nc is cd) return cd;
  cd = nc;
  goto retry;
}

Expr collapse(Expr ex) {
  auto res = mustCast!(Expr)(collapse(fastcast!(Tree)(ex)));
  debug {
    if (ex.valueType() != res.valueType()) {
      logln("collapse has violated type consistency: "[], ex, " => "[], res);
      logln("from: ", (cast(Object)(ex.valueType())).classinfo.name, " ", ex.valueType());
      logln("to: ", (cast(Object)(res.valueType())).classinfo.name, " ", res.valueType());
      fail;
    }
  }
  return res;
}

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
  override void emitLLVM(LLVMFile lf) { }
  mixin defaultIterate!();
  mixin defaultCollapse!();
}

interface Expr : Tree {
  IType valueType();
  override Expr dup();
}

// has a pointer, but please don't modify it - ie. string literals
interface CValue : Expr {
  void emitLocation(LLVMFile);
  override CValue dup();
}

// free to modify
interface LValue : CValue {
  override LValue dup();
}

// more than rvalue, less than lvalue
interface MValue : Expr {
  void emitAssignment(LLVMFile); // eat value from stack and store
  override MValue dup();
}

// used as assignment source placeholder in emitAssignment
class Placeholder : Expr {
  IType type;
  mixin defaultIterate!();
  mixin defaultCollapse!();
  this(IType type) { this.type = type; }
  override IType valueType() { return type; }
  override void emitLLVM(LLVMFile lf) { fail; }
  private this() { }
  mixin DefaultDup!();
}

class Filler : Expr {
  IType type;
  this(IType type) { this.type = type; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      push(lf, "zeroinitializer");
    }
  }
}

// can be printed as string
interface Formatable {
  Expr format(Expr ex);
}

/// Emitting this sets up FLAGS.
/// TODO: how does this work on non-x86?
interface Cond : Iterable {
  void jumpOn(LLVMFile lf, bool cond, string dest);
  override Cond dup();
  Cond collapse(); // like Tree
}

interface IRegister {
  string getReg();
}

class Register(string Reg) : Expr, IRegister {
  override string getReg() { return Reg; }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override IType valueType() { return Single!(SysInt); }
  override void emitLLVM(LLVMFile lf) {
    if (Reg == "ebp") {
      load(lf, "ptrtoint i8* %__stackframe to i32");
      return;
    }
    todo("Register!("~Reg~")::emitLLVM");
    /*if (isARM && Reg == "ebp"[]) {
      af.pushStack("fp"[], 4);
      return;
    }
    af.pushStack("%"~Reg, 4);*/
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
    auto OFFS = lf.exprs.length;
    scope(success) if (lf.exprs.length != OFFS + `~value~`) {
      logln("llvm expr stack unexpected outcome: got "[], lf.exprs.length, "; expected "[], OFFS, " + "[], `~value~`);
      fail();
    }`).ctReplace("\n"[], ""[], "OFFS"[], hash); // fix up line numbers!
}

class CallbackExpr : Expr, HasInfo {
  IType type;
  Expr ex; // held for dg so it can iterate properly
  void delegate(Expr, LLVMFile) dg;
  string info;
  this(string info, IType type, Expr ex, void delegate(Expr, LLVMFile) dg) {
    this.info = info; this.type = type; this.ex = ex; this.dg = dg;
  }
  override {
    string getInfo() { return info; }
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) { dg(ex, lf); }
    string toString() { return Format("callback<"[], ex, ">"[]); }
    mixin defaultIterate!(ex);
    mixin defaultCollapse!();
  }
  private this() { }
  mixin DefaultDup!();
}

interface ScopeLike {
  Stuple!(IType, string)[] stackframe();
  Statement[] getGuards();
  int[] getGuardOffsets();
}

int framelength2(ScopeLike sl) {
  return sl.stackframe().length;
}

string frametype2(ScopeLike sl) {
  string type;
  foreach (entry; sl.stackframe()) {
    if (type) type ~= ", ";
    type ~= typeToLLVM(entry._0);
  }
  return qformat("{", type, "}");
}

string lltypesize(string type) {
  if (type.endsWith("}") || type.startsWith("%")) {
    if (llvmver() < 37) {
      return qformat("ptrtoint(", type, "* getelementptr(", type, "* null, i32 1) to i32)");
    } else {
      return qformat("ptrtoint(", type, "* getelementptr(", type, ", ", type, "* null, i32 1) to i32)");
    }
  }
  logln("llsize(", type, ")");
  fail;
}

string lloffset(string type, string type2, int offs) {
  string expr;
  if (llvmver() >= 37) {
	expr = qformat("ptrtoint(", type2, "* getelementptr(", type, ", ", type, "* null, i32 0, i32 ", offs, ") to i32)");
  } else {
	expr = qformat("ptrtoint(", type2, "* getelementptr(", type, "* null, i32 0, i32 ", offs, ") to i32)");
  }
  return readllex(expr);
}

template DefaultScopeLikeGuards() {
  Statement[] getGuards() {
    if (auto sl = fastcast!(ScopeLike) (sup))
      return sl.getGuards();
    else
      return null;
  }
  int[] getGuardOffsets() {
    if (auto sl = fastcast!(ScopeLike) (sup))
      return sl.getGuardOffsets();
    else
      return null;
  }
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

static int stmt_and_t_marker;

void sae_markercheck(int marker) { // outside the template (because incremental builds)
  // if (marker == 6) asm { int 3; }
}

void sae_debugme(Expr ex, int marker) {
  // if (marker == 6) asm { int 3; }
  // logln(ex);
}

class StatementAnd {
  Statement first;
  Expr second;
}

template StatementAndT(T) {
  class StatementAndT : StatementAnd, T {
    static if (is(T == Expr)) const string NAME = "sae";
    static if (is(T == LValue)) const string NAME = "sal";
    static if (is(T == MValue)) const string NAME = "sam"; // Seriously?
    bool permissive;
    int marker;
    this(Statement first, T second, bool permissive = false) {
      this.first = first;
      this.second = second;
      this.permissive = permissive;
      this.marker = stmt_and_t_marker ++;
      sae_markercheck(marker);
    }
    mixin defaultIterate!(first, second);
    mixin defaultCollapse!();
    bool once;
    bool check() {
      sae_markercheck(marker);
      if (once) {
        if (permissive) return false;
        logln("Double emit "[], marker, " "[], this, ". NOT SAFE. "[]);
        fail;
      }
      once = true;
      return true;
    }
    override {
      string toString() { return Format(NAME, " "[], marker, "{"[], first, second, "}"[]); }
      StatementAndT dup() { return fastalloc!(StatementAndT)(first.dup, fastcast!(T) (second.dup)); }
      IType valueType() { return second.valueType(); }
      void emitLLVM(LLVMFile lf) {
        sae_debugme(this, marker);
        if (check) first.emitLLVM(lf);
        second.emitLLVM(lf);
      }
      static if (is(T: LValue)) void emitLocation(LLVMFile lf) {
        sae_debugme(this, marker);
        if (check) first.emitLLVM(lf);
        fastcast!(T) (second).emitLocation(lf);
      }
      static if (is(T: MValue)) void emitAssignment(LLVMFile lf) {
        sae_debugme(this, marker);
        if (check) first.emitLLVM(lf);
        fastcast!(T) (second).emitAssignment(lf);
      }
    }
  }
}

alias StatementAndT!(Expr) StatementAndExpr;
alias StatementAndT!(LValue) StatementAndLValue;
alias StatementAndT!(MValue) StatementAndMValue;

Expr mkStatementAndExpr(Statement st, Expr ex, bool permissive = false) {
  if (!st) return ex; // convenience
  if (auto mv = fastcast!(MValue) (ex))
    return fastalloc!(StatementAndMValue)(st, mv, permissive);
  if (auto lv = fastcast!(LValue) (ex))
    return fastalloc!(StatementAndLValue)(st, lv, permissive);
  return fastalloc!(StatementAndExpr)(st, ex, permissive);
}

Statement unrollSAE(ref Expr ex) {
  if (auto sae = fastcast!(StatementAndExpr) (ex)) {
    ex = sae.second; return sae.first;
  }
  if (auto sal = fastcast!(StatementAndLValue) (ex)) {
    ex = sal.second; return sal.first;
  }
  if (auto sam = fastcast!(StatementAndMValue) (ex)) {
    ex = sam.second; return sam.first;
  }
  return null;
}

class PlaceholderToken : Expr, HasInfo {
  IType type;
  string info;
  this(IType type, string info) { this.type = type; this.info = info; }
  PlaceholderToken dup() { return this; } // IMPORTANT.
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) { logln("DIAF "[], info, " of "[], type); fail; assert(false); }
    string toString() { return Format("PlaceholderToken("[], info, ")"[]); }
    string getInfo() { return info; }
  }
}

class PlaceholderTokenLV : PlaceholderToken, LValue {
  PlaceholderTokenLV dup() { return this; }
  this(IType type, string info) { super(type, info); }
  override void emitLocation(LLVMFile lf) { assert(false); }
  override string toString() { return Format("PlaceholderLV("[], info, ")"[]); }
}

interface ForceAlignment {
  int alignment(); // return 0 if don't need special alignment after all
}

int delegate(IType)[] alignChecks;

int roundTo(int i, int to) {
  auto i2 = (i / to) * to;
  if (i2 != i) return i2 + to;
  else return i;
}

// TODO tls
int[string] alignment_cache; 

int needsAlignment(IType it) {
  auto hash = it.mangle();
  if (auto p = hash in alignment_cache) return *p;
  int store(int i) { alignment_cache[hash] = i; return i; }
  it = resolveType(it);
  foreach (check; alignChecks)
    if (auto res = check(it)) return store(res);
  const limit = 4;
  it = resolveType(it);
  if (auto fa = fastcast!(ForceAlignment) (it))
    if (auto res = fa.alignment()) return store(res);
  todo(qformat("needsAlignment(", it, ")"));
  return 0;
  // if (it.size > limit) return store(limit);
  // else return store(it.size);
}

version(Windows) { }
else {
  extern(C) {
    struct winsize {
      ushort row, col, xpixel, ypixel;
    }
    int ioctl(int d, int request, ...);
  }
}

extern(C) {
  int fflush(void* stream);
  void* stdin;
}

string prevLogLine;

template logSmart(bool Mode, bool Stderr = false) {
  void logSmart(T...)(T t) {
    auto pretext = Format(t);
    string text;
    foreach (dchar ch; pretext) {
      if (ch == '\t') {
        while (text.length % 8 != 0) text ~= " ";
      } else text ~= ch;
    }
    if (Mode) {
      if (faststreq(text, prevLogLine)) return;
    }
    int col;
    tools.log.log("\r"[]);
    version(Windows) { col = 80; }
    else {
      winsize ws;
      ioctl(0, /*TIOCGWINSZ*/0x5413, &ws);
      col = ws.col;
    }
    string empty;
    for (int i = 0; i < col - 1; ++i) empty ~= " ";
    tools.log.log("\r"[], empty, "\r"[]);
    
    static if (Stderr) {
      static assert(!Mode);
      fprintf(stderr, "%s\n", toStringz(text));
    } else {
      tools.log.log(text);
      
      if (Mode) tools.log.log("\r"[]);
      else tools.log.log("\n"[]);
    }
    fflush(stdin);
  }
}

extern(C) void _line_numbered_statement_emitLLVM(LineNumberedStatement, LLVMFile);

interface LineNumberedStatement : Statement {
	LineNumberedStatement dup();
	void configPosition(string text);
	void getInfo(ref string name, ref int line, ref int column);
}

class LineNumberedStatementClass : LineNumberedStatement {
  int line, column;
  string name, source;
  abstract LineNumberedStatement dup();
  abstract void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical);
  override void getInfo(ref string n, ref int l, ref int c) { n = name; l = line; c = column; }
  override void configPosition(string text) {   
    source = text;
    auto pos = lookupPos(text);
    line = pos._0;
    column = pos._1;
    name = pos._2;
  }
  override void emitLLVM(LLVMFile lf) {
    _line_numbered_statement_emitLLVM(this, lf);
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
  registerClass("ast.base"[], new Register!("ebp"[]));
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

// react to more errors with return null; useful for C parsing
TLS!(bool) lenient;
static this() { New(lenient); }

interface Dependency {
  void emitDependency(LLVMFile lf);
}

extern(C) int atoi(char*);
bool my_atoi(string s, out int i) {
  s = s.mystripl();
  if (!s.length) return false;
  if (s == "0") return true;
  bool neg;
  if (s[0] == '-') { s = s[1..$]; neg = true; }
  if (!s.length) return false;
  foreach (ch; s) {
    if (ch < '0' || ch > '9') return false;
    byte b = ch - '0';
    i = i * 10 + b;
  }
  if (neg) i = -i;
  return true;
}

class NamedNull : NoOp, Named, SelfAdding {
  override string getIdentifier() { return null; }
  override bool addsSelf() { return true; }
}

class PassthroughWeakNoOp : NoOp, IsMangled {
  IsMangled[] targets;
  this(IsMangled[] targets...) { this.targets = targets.dup; }
  string mangleSelf() { return null; }
  void markWeak() { foreach (tar; targets) tar.markWeak(); }
  void markExternC() { foreach (tar; targets) tar.markExternC(); }
}

extern(C) void printThing(LLVMFile lf, string s, Expr ex);

class VoidExpr : Expr {
  override {
    mixin defaultIterate!();
    mixin defaultCollapse!();
    VoidExpr dup() { return this; }
    IType valueType() { return Single!(Void); }
    void emitLLVM(LLVMFile lf) { push(lf, "void"); }
  }
}

interface IModule : Named {
  string filename();
  string modname();
  bool getDontEmit();
  bool getDoneEmitting();
  void addEntry(Tree);
}

TLS!(IModule) current_module;

// some namespaces behave differently when used in a using() statement than in property mode (a.b)
interface WithAware {
  Object forWith();
}

// object that is created a lot and that we may be interested in cleaning up if it's not needed
interface Temporary {
  void cleanup(bool deeply);
  void markNeeded();
}

void cleanupex(Expr ex, bool deeply) {
  if (auto t = fastcast!(Temporary)(ex))
    t.cleanup(deeply);
}

// cheap to access multiple times, cheap to flatten into tuple
enum CheapMode { Multiple, Flatten }
extern(C) bool _is_cheap(Expr ex, CheapMode mode);

// for the purpose of emitting asm, this can be treated as a unit
// for instance, modules and functions
// this is so expressions can "see" if their context is already being emat,
// and ie. abort if it is
interface EmittingContext {
  bool isBeingEmat();
}

enum ImportType {
  Regular, Public, Static
}

// for instance, a template instance modifies the name of all types and variables inside it.
interface ModifiesName {
  string modify(string);
}

bool readIndexShorthand(string name, ref int i) {
  auto idxstr = name.startsWith("_"[]);
  if (!idxstr || !my_atoi(idxstr, i)) return false;
  return true;
}

Object delegate(Object) getOpCall;

Expr True, False;
Cond cTrue, cFalse;

const esp_alignment_delta = 8; // call, push ebp

extern(C) Expr _buildFunCall(Object obj, Expr arg, string info);
Expr buildFunCall(Object obj, Expr arg, string info) {
  return _buildFunCall(obj, arg, info);
}

interface Iterator {
  IType elemType();
  Cond testAdvance(LValue); // false => couldn't get a value
  Expr currentValue(Expr);
}

interface RichIterator : Iterator {
  Expr length(Expr);
  Expr index(Expr, Expr pos);
  Expr slice(Expr, Expr from, Expr to);
}

interface RangeIsh {
  Expr getPos(Expr base);
  Expr getEnd(Expr base);
}

interface StructLike : Named {
  bool immutableNow();
  bool isPacked();
  int numMembers();
}

static this() {
  alignChecks ~= (IType it) {
    if (isWindoze() && Single!(Double) == resolveType(it)) return 8;
    return 0;
  };
}

int llval_count;
class LLVMValue : Expr {
  string str;
  IType type;
  int count;
  this(string s, IType type = null) {
    str = s;
    if (!type) type = Single!(SysInt);
    this.type = type;
    this.count = llval_count++;
    // if (count == 5961) fail;
  }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    string toString() { return qformat("ll(", str, ")"); }
    LLVMValue dup() { return this; }
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      if (!str) {
        logln("llval(", count, ") of ", type, " not initialized");
        fail;
      }
      lf.push(str);
    }
  }
}

extern(C) Expr fcc_wte_collapse(WithTempExpr);

class WithTempExpr : Expr {
  LLVMValue val; LLVMRef lltemp;
  Expr thing, superthing;
  this(Expr thing, Expr delegate(Expr, LLVMRef) dg) {
    this(thing);
    superthing = dg(val, lltemp);
  }
  this(Expr thing) { // delayed setup. WARN: expert use only!
    val = fastalloc!(LLVMValue)(cast(string) null, thing.valueType());
    lltemp = fastalloc!(LLVMRef)();
    this.thing = thing;
  }
  this() { }
  void copy(WithTempExpr wte) {
    val        = wte.val;
    lltemp     = wte.lltemp;
    thing      = wte.thing;
    superthing = wte.superthing;
  }
  // did the dg() succeed?
  bool isValid() { return !!superthing; }
  mixin defaultIterate!(thing, superthing);
  WithTempExpr create() { return fastalloc!(WithTempExpr)(); }
  override {
    Expr collapse() { return fcc_wte_collapse(this); }
    string toString() {
      return Format("<with temp "[], thing, ": "[], superthing, ">"[]);
    }
    Expr dup() {
      auto res = create();
      res.val = fastalloc!(LLVMValue)(cast(string) null, val.type);
      res.lltemp = fastalloc!(LLVMRef)();
      if (lltemp.type) res.lltemp.type = lltemp.type;
      void replace(ref Iterable it) {
        if (it is val) it = res.val;
        else if (it is lltemp) it = res.lltemp;
        else it.iterate(&replace);
      }
      res.thing = thing.dup;
      res.superthing = superthing.dup;
      res.superthing.iterate(&replace);
      return res;
    }
    IType valueType() { return superthing.valueType(); }
    void emitLLVM(LLVMFile lf) {
      mixin(mustOffset("1"));
      val.str = save(lf, thing);
      // logln("set val(", val.count, ") str to '", val.str, "'");
      if (lltemp.type) {
        lltemp.allocate(lf);
        lltemp.begin(lf);
      }
      superthing.emitLLVM(lf);
      if (lltemp.type) {
        lltemp.end(lf);
      }
    }
  }
}

class WithTempMValue : WithTempExpr, MValue {
  bool alreadyUsed;
  this(Expr thing) { super(thing); }
  this() { }
  override {
    MValue dup() { return fastcast!(MValue)(super.dup()); } // type works out due to create()
    WithTempExpr create() { return fastalloc!(WithTempMValue)(); }
    string toString() { return Format("<with temp (mvalue) "[], thing, ": "[], superthing, ">"[]); }
    void emitLLVM(LLVMFile lf) {
      if (alreadyUsed) fail; alreadyUsed = true;
      super.emitLLVM(lf);
    }
    void emitAssignment(LLVMFile lf) {
      if (alreadyUsed) fail; alreadyUsed = true;
      auto supermv = fastcast!(MValue)(superthing);
      if (!supermv) fail;
      val.str = save(lf, thing);
      if (lltemp.type) {
        lltemp.allocate(lf);
        lltemp.begin(lf);
      }
      supermv.emitAssignment(lf);
      if (lltemp.type) {
        lltemp.end(lf);
      }
    }
  }
}

class ZeroInitializer : Expr {
  IType type;
  this(IType type) { this.type = type; }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    string toString() { return "{0}"; }
    ZeroInitializer dup() { return fastalloc!(ZeroInitializer)(type); }
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      push(lf, " zeroinitializer");
    }
  }
}

int lr_count;
class LLVMRef : LValue {
  string location;
  IType type;
  int count;
  int state;
  this() {
    count = lr_count ++;
    // if (count == 124) fail;
  }
  this(IType it) { this(); type = it; }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  void allocate(LLVMFile lf) {
    if (location) { logln("double emit? ", this); fail; }
    if (state != 0) fail;
    state = 1;
    
    if (Single!(Void) == type) return;
    location = alloca(lf, "1", typeToLLVM(type));
  }
  void begin(LLVMFile lf) {
    if (state != 1) fail;
    state = 2;
    
    if (Single!(Void) == type) return;
    if (!location) fail;
    auto i8loc = bitcastptr(lf, typeToLLVM(type), "i8", location);
    if (once(lf, "intrinsic llvm.lifetime.start"))
      lf.decls["llvm.lifetime.start"] = "declare void @llvm.lifetime.start(i64, i8* nocapture)";
    put(lf, "call void @llvm.lifetime.start(i64 ", type.llvmSize(), ", i8* ", i8loc, ")");
  }
  void end(LLVMFile lf) {
    if (state != 2) fail;
    state = 3;
    
    if (Single!(Void) == type) return;
    if (!location) fail;
    auto i8loc = bitcastptr(lf, typeToLLVM(type), "i8", location);
    if (once(lf, "intrinsic llvm.lifetime.end"))
      lf.decls["llvm.lifetime.end"] = "declare void @llvm.lifetime.end(i64, i8* nocapture)";
    put(lf, "call void @llvm.lifetime.end(i64 ", type.llvmSize(), ", i8* ", i8loc, ")");
  }
  override {
    string toString() { return qformat("llref(", type, "){", Format(cast(void*) this), "}"); }
    LLVMRef dup() { return this; }
    IType valueType() { if (!type) fail; return type; }
    void emitLLVM(LLVMFile lf) {
      if (!location) fail;
      if (state != 2) fail;
      load(lf, ll_load(typeToLLVM(type), location));
    }
    void emitLocation(LLVMFile lf) {
      if (!location) fail;
      if (state != 2) fail;
      push(lf, location);
    }
  }
}

extern(C) Expr llvmvalstr(string s);

string cqformat(int i) {
  switch (i) {
    case -1: return "-1";
    case 0 : return  "0"; case  1: return  "1"; case  2: return  "2"; case  3: return  "3";
    case 4 : return  "4"; case  5: return  "5"; case  6: return  "6"; case  7: return  "7";
    case 8 : return  "8"; case  9: return  "9"; case 10: return "10"; case 11: return "11";
    case 12: return "12"; case 13: return "13"; case 14: return "14"; case 15: return "15";
    case 16: return "16"; case 17: return "17"; case 18: return "18"; case 19: return "19";
    default: return qformat(i);
  }
}

Expr llvmval(T...)(T t) {
  static if (is(T == string)) return llvmvalstr(t);
  else static if (is(T == int)) return llvmvalstr(cqformat(t));
  else return llvmvalstr(qformat(t));
}

bool isnum(string s, out int i) { return my_atoi(s, i); }

string lladd(string a, string b) {
  int k, l;
  if (isnum(a, k) && isnum(b, l)) return cqformat(k+l);
  return qformat("add (i32 ", a, ", i32 ", b, ")");
}
string llsub(string a, string b) {
  int k, l;
  if (isnum(a, k) && isnum(b, l)) return cqformat(k-l);
  return qformat("sub (i32 ", a, ", i32 ", b, ")");
}
string llmul(string a, string b) {
  int k, l;
  if (isnum(a, k) && isnum(b, l)) return cqformat(k*l);
  return qformat("mul (i32 ", a, ", i32 ", b, ")");
}
string lldiv(string a, string b) {
  int k, l;
  if (isnum(a, k) && isnum(b, l)) return cqformat(k/l);
  return qformat("div (i32 ", a, ", i32 ", b, ")");
}
bool llmax_decompose_first(string s, out int i, out string k) {
  if (auto rest = s.startsWith("select(i1 icmp sgt(i32 ")) {
    int num;
    my_atoi(rest.slice(" "), num);
    auto reconstruct_a = cqformat(num);
    auto start = qformat("select(i1 icmp sgt(i32 ", reconstruct_a, ", i32 ");
    if (auto rest2 = s.startsWith(start)) {
      auto twoblength = s.length - start.length - "), i32 ".length - reconstruct_a.length - ", i32 ".length - ")".length;
      auto blength = twoblength / 2;
      auto b = rest2[0..blength];
      if (s == qformat(start, b, "), i32 ", reconstruct_a, ", i32 ", b, ")")) {
        i = num;
        k = b;
        return true;
      } else {
        logln("bad reconstruct: ", s, " TO ", b);
        fail;
      }
    }
  }
  return false;
}
bool is_structsize(string s, out string res) {
  if (auto rest = s.startsWith("i32 ptrtoint(")) {
    auto r2len = rest.length - "* getelementptr(".length - "* null, i32 1) to i32)".length;
    auto rlen = r2len / 2;
    auto r = rest[0..rlen];
    if (s == qformat("i32 ptrtoint(", r, "* getelementptr(", r, "* null, i32 1) to i32)")) {
      res = r;
      return true;
    } else {
      logln("bad reconstruct: ", s, " to ", r);
      fail;
    }
  }
  return false;
}

import cache;

string llmax(string a, string b) {
  // a = llexcachecheck(a); // doesn't help
  // b = llexcachecheck(b);
  if (a == b) return a;
  int k, l; string k2, l2;
  if (isnum(a, k) && isnum(b, l)) return cqformat((k>l)?k:l);
  if (!isnum(a, k) && isnum(b, l)) { auto temp = a; a = b; b = temp; }
  if (isnum(a, k) && k <= 4 && b.find("i32") != -1) return b; // HAAAAAAAAAAX
  if (is_structsize(a, k2) && is_structsize(b, l2)) {
    if (k2.startsWith(l2)) return k2;
    if (l2.startsWith(k2)) return l2;
  }
  if (llmax_decompose_first(b, l, l2)) {
    if (isnum(a, k)) {
      return llmax(cqformat((k>l)?k:l), l2);
    } else {
      return llmax(cqformat(l), a, l2);
    }
  }
  /*if (isnum(a, k) || isnum(b, l)) {
    logln("llmax(", a, ", ", b, ")");
  }*/
  /*auto sz1 = readllex(a);
  auto sz2 = readllex(b);
  if (isnum(sz1, k) && isnum(sz2, l)) return cqformat((k>l)?k:l);
  fail;*/
  auto expr = qformat("select(i1 icmp sgt(i32 ", a, ", i32 ", b, "), i32 ", a, ", i32 ", b, ")");
  // if (expr.length < 512) return expr;
  return readllex(expr);
}
string llmax(string a, string b, string c) { return llmax(a, llmax(b, c)); }

string llAlign(string a, IType it) {
  auto sz = it.llvmSize();
  return llmul(lldiv(lladd(a, llsub(sz, "1")), sz), sz);
}

// for unruly identifiers
string refcompress(string s) {
  string res;
  int[string] seen;
  void add(string s) { if (res) res ~= "_"; res ~= s; }
  foreach (i, part; s.split("_")) {
    if (auto prev = part in seen) {
      auto d = i - *prev;
      add(qformat("b", d));
    } else add(part);
    seen[part] = i;
  }
  return res;
}

struct PropArgs {
  bool withTuple = true, withCall = true, withCallOnTuple = true;
}

extern(C) string mangletree(Tree tr);

template memoize(alias Fun, alias Var, string Name) {
  mixin(`
    Ret!(typeof(&Fun)) `~Name~`(Params!(typeof(&Fun)) par) {
      if (!Var) Var = Fun(par);
      return Var;
    }`);
}

class NamedArg : Expr {
  Expr base;
  string name, reltext;
  this(string name, string text, Expr base) { this.name = name; this.reltext = text; this.base = base; }
  override {
    string toString() { return Format(name, " => "[], base); }
    IType valueType() { return base.valueType(); }
    NamedArg dup() { return fastalloc!(NamedArg)(name, reltext, base.dup); }
    mixin defaultIterate!(base);
    mixin defaultCollapse!();
    void emitLLVM(LLVMFile lf) {
      base.emitLLVM(lf);
      // reltext.failparse("Named argument ", name, " could not be assigned to a function call! ");
    }
  }
}

extern(C) string prettyprint(Iterable itr);

template mustCast(T) {
  T mustCast(U)(U u) {
    auto res = fastcast!(T)(u);
    if (!res) {
      logln("Failed to convert to ", T.stringof, ": ");
      logln("> ", u);
      fail;
    }
    return res;
  }
}

interface ArrayLiteralExpr {
  int getLength();
}
