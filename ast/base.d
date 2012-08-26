module ast.base;

public import asmfile, ast.types, parseBase, errors, tools.log: logln;

public import casts, alloc, quickformat;

import tools.base: Format, New, This_fn, rmSpace;
import tools.ctfe: ctReplace;

const string EXT = ".nt";

string path_prefix, platform_prefix;

bool isWindoze() {
  return platform_prefix.find("mingw"[]) != -1;
}

bool isARM() {
  return !!platform_prefix.startsWith("arm-"[]);
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
    override void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {";
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
                logln(this, ": cannot substitute ", $A, " with ", res, ": ", typeof($A).stringof, " expected! ");
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
    if (isARM && Reg == "ebp"[]) {
      af.pushStack("fp"[], 4);
      return;
    }
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
      logln("Stack offset violated: got "[], af.currentStackDepth, "; expected "[], OFFS, " + "[], `~value~`);
      fail();
    }`).ctReplace("\n"[], ""[], "OFFS"[], hash); // fix up line numbers!
}

class CallbackExpr : Expr, HasInfo {
  IType type;
  Expr ex; // held for dg so it can iterate properly
  void delegate(Expr, AsmFile) dg;
  string info;
  this(string info, IType type, Expr ex, void delegate(Expr, AsmFile) dg) {
    this.info = info; this.type = type; this.ex = ex; this.dg = dg;
  }
  override {
    string getInfo() { return info; }
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { dg(ex, af); }
    string toString() { return Format("callback<"[], ex, ">"[]); }
    mixin defaultIterate!(ex);
  }
  private this() { }
  mixin DefaultDup!();
}

interface ScopeLike {
  int framesize();
  Statement[] getGuards();
  int[] getGuardOffsets();
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
      void emitAsm(AsmFile af) {
        sae_debugme(this, marker);
        if (check) first.emitAsm(af);
        second.emitAsm(af);
      }
      static if (is(T: LValue)) void emitLocation(AsmFile af) {
        sae_debugme(this, marker);
        if (check) first.emitAsm(af);
        fastcast!(T) (second).emitLocation(af);
      }
      static if (is(T: MValue)) void emitAssignment(AsmFile af) {
        sae_debugme(this, marker);
        if (check) first.emitAsm(af);
        fastcast!(T) (second).emitAssignment(af);
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
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { logln("DIAF "[], info, " of "[], type); fail; assert(false); }
    string toString() { return Format("PlaceholderToken("[], info, ")"[]); }
    string getInfo() { return info; }
  }
}

class PlaceholderTokenLV : PlaceholderToken, LValue {
  PlaceholderTokenLV dup() { return this; }
  this(IType type, string info) { super(type, info); }
  override void emitLocation(AsmFile af) { assert(false); }
  override string toString() { return Format("PlaceholderLV("[], info, ")"[]); }
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

// TODO tls
int[string] alignment_cache; 

int needsAlignment(IType it) {
  auto hash = it.mangle();
  if (auto p = hash in alignment_cache) return *p;
  int store(int i) { alignment_cache[hash] = i; return i; }
  foreach (check; alignChecks)
    if (auto res = check(it)) return store(res);
  const limit = 4;
  it = resolveType(it);
  if (auto fa = fastcast!(ForceAlignment) (it))
    if (auto res = fa.alignment()) return store(res);
  if (it.size > limit) return store(limit);
  else return store(it.size);
}

void doAlign(ref int offset, IType type) {
  int to = needsAlignment(type);
  if (!to) return; // what. 
  offset = roundTo(offset, to);
}

int getFillerFor(IType t, int depth) {
  if (Single!(Void) == t) return 0;
  auto nd = -align_boffs(t, depth) - t.size;
  return nd - depth;
}

int alignStackFor(IType t, AsmFile af) {
  auto delta = getFillerFor(t, af.currentStackDepth);
  af.salloc(delta);
  return delta;
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

template logSmart(bool Mode) {
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
    tools.log.log(text);
    if (Mode) tools.log.log("\r"[]);
    else tools.log.log("\n"[]);
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
  abstract void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical);
  override void getInfo(ref string n, ref int l) { n = name; l = line; }
  override void configPosition(string text) {   
    auto pos = lookupPos(text);
    line = pos._0;
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

import tools.base: Stuple;
TLS!(Stuple!(string, IType)) templInstOverride;
static this() { New(templInstOverride); }

TLS!(string) currentPropBase;
static this() { New(currentPropBase); }

// react to more errors with return null; useful for C parsing
TLS!(bool) lenient;
static this() { New(lenient); }

interface Dependency {
  void emitDependency(AsmFile af);
}

extern(C) int atoi(char*);
int my_atoi(string s) {
  auto mew = qformat(s, "\x00"[]);
  return atoi(mew.ptr);
}

class NamedNull : NoOp, Named, SelfAdding {
  override string getIdentifier() { return null; }
  override bool addsSelf() { return true; }
}

void armpush(AsmFile af, string base, int size, int offset = 0) {
  if (size == 1) {
    af.mmove1(qformat("["[], base, "[], #"[], offset, "]"[]), "r0"[]);
    af.salloc(1);
    af.mmove1("r0"[], "[sp]"[]); // full stack
    return;
  }
  if (size == 2) {
    af.mmove2(qformat("["[], base, "[], #"[], offset, "]"[]), "r0"[]);
    af.salloc(2);
    af.mmove2("r0"[], "[sp]"[]); // full stack
    return;
  }
  if (size % 4 || !size) { logln("!! "[], size); fail; }
  for (int i = size / 4 - 1; i >= 0; --i) {
    af.mmove4(qformat("["[], base, "[], #"[], offset + i * 4, "]"[]), "r0"[]);
    af.pushStack("r0"[], 4);
  }
}

void armpop(AsmFile af, string base, int size, int offset = 0) {
  if (base == "r0"[]) { logln("bad register use"[]); fail; }
  if (size == 1) {
    af.mmove1("[sp]"[], "r0"[]);
    af.sfree(1);
    af.mmove1("r0"[], qformat("["[], base, "[], #"[], offset, "]"[]));
    return;
  }
  if (size == 2) {
    af.mmove2("[sp]"[], "r0"[]);
    af.sfree(2);
    af.mmove2("r0"[], qformat("["[], base, "[], #"[], offset, "]"[]));
    return;
  }
  if (size % 4 || !size) { logln("!! "[], size); fail; }
  for (int i = 0; i < size / 4; ++i) {
    af.popStack("r0"[], 4);
    af.mmove4("r0"[], qformat("["[], base, "[], #"[], offset + i * 4, "]"[]));
  }
}
extern(C) void printThing(AsmFile af, string s, Expr ex);

class VoidExpr : Expr {
  override {
    mixin defaultIterate!();
    VoidExpr dup() { return this; }
    IType valueType() { return Single!(Void); }
    void emitAsm(AsmFile af) { }
  }
}

class OffsetExpr : LValue {
  int offset;
  IType type;
  this(int o, IType i) { offset = o; type = i; }
  mixin defaultIterate!();
  override {
    string toString() {
      if (offset == int.max)
        return Format("open offset<"[], type, ">"[]);
      return Format("offset<"[], type, "> at "[], offset);
    }
    OffsetExpr dup() { return this; } // can't dup, is a marker
    IType valueType() { return type; }
    void emitAsm(AsmFile af) {
      if (offset == int.max) fail;
      if (isARM) {
        armpush(af, "fp"[], type.size, offset);
      } else {
        af.pushStack(qformat(offset, "(%ebp)"[]), type.size);
      }
    }
    void emitLocation(AsmFile af) {
      af.loadOffsetAddress(af.stackbase, offset, af.regs[0]);
      af.pushStack(af.regs[0], 4);
    }
  }
}

interface IModule : Named {
  string filename();
  string modname();
  bool getDontEmit();
  bool getDoneEmitting();
}

TLS!(IModule) current_module;

// some namespaces behave differently when used in a using() statement than in property mode (a.b)
interface WithAware {
  Object forWith();
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
  if (!idxstr) return false;
  auto idx = my_atoi(idxstr);
  if (idxstr != Format(idx))
    return false;
  i = idx;
  return true;
}

Object delegate(Object) getOpCall;

Expr True, False;
Cond cTrue, cFalse;

const esp_alignment_delta = 8; // call, push ebp
