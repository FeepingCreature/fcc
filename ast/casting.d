module ast.casting;

import ast.base, ast.parse, ast.int_literal;

class RC {
  Expr from;
  IType to;
}

template ReinterpretCast_Contents(T) {
  this(IType to, T from, bool allowCValue = false) {
    this.from = from;
    this.to = to;
    static if (is(T==Expr)) {
      if (!allowCValue && (fastcast!(LValue)~ from || fastcast!(CValue)~ from)) {
        logln(this, "? Suure? "[]);
        fail;
      }
    }
    // if (to.size != from.valueType().size) fail;
    auto fromtype = from.valueType();
    if (to.llvmType() != fromtype.llvmType() && to.llvmSize() != fromtype.llvmSize()) {
      logln("Can't cast "[], from);
      logln();
      logln("from: ", from.valueType());
      logln("to:   ", to);
      logln("size: ", from.valueType().llvmSize(), " vs. "[], to.llvmSize(), "!"[]);
      fail();
    }
  }
  private this() { }
  typeof(this) dup() { return fastalloc!(typeof(this))(to, fastcast!(T) (from.dup), true); }
  // mixin defaultIterate!(from);
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    auto backup = from;
    defaultIterate!(from).iterate(dg, mode);
    /*if (from !is backup) {
      if (auto rce = fastcast!(RCE)(from)) {
        logln("substituted ", backup);
        logln("into ", from);
        fail;
      }
    }*/
    auto new_from_test = fastcast!(T) (from);
    if (!new_from_test/* || from.valueType().size != backup.valueType().size*/) {
      logln("Missubstitution!"[]);
      logln("In cast of "[], T.stringof);
      logln("Was: "[], backup, " ", backup.valueType());
      logln(" To: "[], from, " ", from.valueType());
      fail;
    }
  }
  Expr collapse() {
    if (from.valueType() == to) {
      return from;
    }
    auto from = .collapse(from);
    if (auto rce2 = fastcast!(RCE) (from)) {
      return reinterpret_cast(to, .collapse(rce2.from));
    }
    if (auto wte = fastcast!(WithTempExpr)(from)) {
      wte = fastcast!(WithTempExpr)(wte.dup);
      wte.superthing = .collapse(reinterpret_cast(to, wte.superthing));
      return wte;
    }
    return this;
  }
  override {
    static if (is(typeof((fastcast!(T)~ from).emitLocation(null))))
      void emitLocation(LLVMFile lf) {
        (fastcast!(T)~ from).emitLocation(lf);
        auto fvt = from.valueType();
        auto from = typeToLLVM(fvt)~"*", to = typeToLLVM(to)~"*";
        if (from != to) {
          llcast(lf, from, to, lf.pop(), fvt.llvmSize());
        }
      }
    static if (is(typeof((fastcast!(T)~ from).emitAssignment(null))))
      void emitAssignment(LLVMFile lf) {
        llcast(lf, typeToLLVM(to), typeToLLVM(from.valueType()), lf.pop(), from.valueType().llvmSize());
        (fastcast!(T)~ from).emitAssignment(lf);
      }
  }
}

template ReinterpretCast(T) {
  static if (is(T==Expr)) {
    class ReinterpretCast : RC, Expr, HasInfo {
      mixin ReinterpretCast_Contents!(Expr);
      override {
        string toString() { return Format("("[], to, ": "[], from, ")"[]); }
        IType valueType() { return to; }
        string getInfo() { return Format(to, ":"[]); }
        void emitLLVM(LLVMFile lf) {
          _reinterpret_cast_expr(this, lf);
        }
      }
    }
  } else static if (is(T==LValue)) {
    final class ReinterpretCast : ReinterpretCast!(CValue), T {
      static const isFinal = true;
      mixin ReinterpretCast_Contents!(T);
    }
  } else {
    class ReinterpretCast : ReinterpretCast!(Expr), T {
      mixin ReinterpretCast_Contents!(T);
    }
  }
}

alias ReinterpretCast!(Expr) RCE;
alias ReinterpretCast!(CValue) RCC;
alias ReinterpretCast!(LValue) RCL; // class LCL omitted due to tang-related concerns
alias ReinterpretCast!(MValue) RCM;
extern(C) void _reinterpret_cast_expr(RCE, LLVMFile);
extern(C) bool _exactly_equals(IType a, IType b);

bool exactlyEquals(IType a, IType b) { return _exactly_equals(a, b); }

// IType parameter is just advisory!
// Functions may ignore it.
Expr delegate(Expr, IType)[] converts;

Expr tryConvert(Expr ex, IType dest) {
  Expr res;
  foreach (dg; converts) {
    auto ex2 = dg(ex, dest);
    if (ex2 && ex2.valueType() == dest) {
      res = ex2;
      break;
    }
  }
  return res;
}

Expr genCastFor(Expr ex, IType dest, string text) {
  // implicit-default cast
  {
    auto ex2 = ex;
    try {
      if (!gotImplicitCast(ex2, dest, (IType it) { return test(it == dest); })) {
        // text.setError("can't get "[], ex.valueType(), " into "[], dest);
        text.setError("types don't match in explicit-cast: ", ex.valueType(), " into ", dest);
      }
    } catch (Exception ex) {
      text.failparse(ex);
    }
    
    // confirm
    if (ex2.valueType() == dest) return reinterpret_cast(dest, ex2);
  }
  // conversion cast
  {
    auto ex2 = forcedConvert(ex);
    if (auto res = tryConvert(ex2, dest)) return res;
  }
  // reinterpret cast
  {
    IType[] types;
    auto ex2 = ex;
    if (!gotImplicitCast(ex2, dest, (IType it) { types ~= it; return it.llvmSize() == dest.llvmSize(); })) {
      text.setError("Expression not matched in cast; none of "[], types, " matched "[], dest.llvmSize(), ". "[]);
    } else {
      if (!!fastcast!(StructLike)(resolveType(dest)) && showsAnySignOfHaving(fastalloc!(Placeholder)(dest), "init")) {
        text.failparse("requested cast to struct that has init function, but init didn't match and we fell back to reinterpret-cast - this is probably not what you wanted");
      }
      return reinterpret_cast(dest, ex2);
    }
  }
  return null;
}

// regular form: type:expr
Object gotCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  IType dest;
  if (!rest(t2, "type"[], &dest) || !t2.accept(":"[]))
    return null;
  if (t2.accept(":"[])) return null;
  dest = forcedConvert(dest);
  if (!rest(t2, "tree.expr _tree.expr.bin"[], &ex)) {
    t2.failparse("Failed to get expression"[]);
  }
  if (auto res = fastcast!(Object)(genCastFor(ex, dest, text))) {
    text = t2;
    resetError;
    return res;
  }
  return null;
}
mixin DefaultParser!(gotCastExpr, "tree.expr.cast"[], "2418"[]);

import tools.base: toDg;

// implicit conversions
struct implicits { static {
  void delegate(Expr, IType, bool delegate(Expr, int))[] dgs;
  void opCatAssign(void delegate(Expr, IType, bool delegate(Expr, int)) dg) {
    dgs ~= dg;
  }
  void opCatAssign(void delegate(Expr, IType, void delegate(Expr, int)) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, bool delegate(Expr, int) dg2) {
      dg(ex, it, (Expr ex, int delta) { dg2(ex, delta); });
    };
  }
  void opCatAssign(void delegate(Expr, IType, void delegate(Expr)) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, bool delegate(Expr, int) dg2) {
      dg(ex, it, (Expr ex) { dg2(ex, 0); });
    };
  }
  void opCatAssign(void delegate(Expr, IType, bool delegate(Expr)) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, bool delegate(Expr, int) dg2) {
      dg(ex, it, (Expr ex) { return dg2(ex, 0); });
    };
  }
  void opCatAssign(void delegate(Expr, bool delegate(Expr)) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, bool delegate(Expr, int) dg2) {
      dg(ex, (Expr ex) { return dg2(ex, 0); });
    };
  }
  void opCatAssign(void delegate(Expr, void delegate(Expr)) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, bool delegate(Expr, int) dg2) {
      dg(ex, (Expr ex) { dg2(ex, 0); });
    };
  }
  void opCatAssign(Expr delegate(Expr) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, bool delegate(Expr, int) dg2) {
      if (auto res = dg(ex)) dg2(res, 0);
    };
  }
  void opCatAssign(Expr delegate(Expr, IType) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, bool delegate(Expr, int) dg2) {
      if (auto res = dg(ex, it)) dg2(res, 0);
    };
  }
  void opCatAssign(Expr function(Expr) fn) {
    opCatAssign(toDg(fn));
  }
  int opApply(int delegate(ref typeof(dgs[0])) callback) {
    foreach (dg; dgs)
      if (auto res = callback(dg)) return res;
    return 0;
  }
}}

class DontCastMeExpr : Expr {
  Expr sup;
  this(Expr sup) { this.sup = sup; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(sup);
  mixin defaultCollapse!();
  override {
    IType valueType() { return sup.valueType(); }
    void emitLLVM(LLVMFile lf) { sup.emitLLVM(lf); }
    string toString() { return Format("__dcm("[], sup, ")"[]); }
  }
}

class DontCastMeCValue : DontCastMeExpr, CValue {
  this(CValue cv) { super(cv); }
  typeof(this) dup() { return new typeof(this)(fastcast!(CValue) (sup.dup)); }
  override void emitLocation(LLVMFile lf) { (fastcast!(CValue)~ sup).emitLocation(lf); }
}

class DontCastMeLValue : DontCastMeCValue, LValue {
  this(LValue lv) { super(lv); }
  typeof(this) dup() { return new typeof(this)(fastcast!(LValue) (sup.dup)); }
}

class DontCastMeMValue : DontCastMeExpr, MValue {
  this(MValue mv) { super(mv); }
  override typeof(this) dup() { return new typeof(this)(fastcast!(MValue) (sup.dup)); }
  override void emitAssignment(LLVMFile lf) { (fastcast!(MValue) (sup)).emitAssignment(lf); }
}

Expr dcm(Expr ex) {
  if (auto lv = fastcast!(LValue)~ ex) return fastalloc!(DontCastMeLValue)(lv);
  else if (auto cv = fastcast!(CValue)~ ex) return fastalloc!(DontCastMeCValue)(cv);
  else if (auto mv = fastcast!(MValue) (ex)) return fastalloc!(DontCastMeMValue)(mv);
  else return fastalloc!(DontCastMeExpr)(ex);
}

Object gotDCMExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (t2.accept("__dcm("[]) && rest(t2, "tree.expr"[], &ex) && t2.accept(")"[])) {
    text = t2;
    return fastalloc!(DontCastMeExpr)(ex);
  } else return null;
}
mixin DefaultParser!(gotDCMExpr, "tree.expr.dcm"[], "53"[]);

import tools.threads: TLS;
import ast.namespace;
TLS!(IType[]) gotImplicitCast_visited_cache; // we go in here a lot, so this pays off
static this() { New(gotImplicitCast_visited_cache, { return &(new Stuple!(IType[]))._0; }); }
bool gotImplicitCast(ref Expr ex, IType want, bool delegate(Expr) accept, int mayFreeRejects = 1, int* scorep = null) {
  if (!ex) fail;
  auto ns = namespace();
  if (!ns) namespace.set(new NoNameSpace); // lots of stuff does namespace().get!() .. pacify it
  scope(exit) namespace.set(ns);
  auto visited = *gotImplicitCast_visited_cache.ptr();
  *gotImplicitCast_visited_cache.ptr() = null; // allow recursion
  scope(exit) *gotImplicitCast_visited_cache.ptr() = visited;
  int visited_offs;
  void addVisitor(IType it) {
    if (visited_offs < visited.length)
      visited[visited_offs++] = it;
    else { own_append(visited, it); visited_offs ++; }
  }
  // want = resolveType(want);
  bool haveVisited(Expr ex) {
    auto t1 = ex.valueType();
    foreach (t2; visited[0 .. visited_offs]) if (t2 == t1) return true;
    return false;
  }
  
  Stuple!(Temporary, int)[] cleanups;
  scope(success) foreach (c; cleanups) c._0.cleanup(c._1 == 1);
  
  Expr recurse(Expr ex, int score, int* score_res) {
    Expr[] recurseInto;
    int[] scoredelta;
    foreach (dg; implicits) {
      Expr res;
      dg(ex, want, (Expr ce, int newscore /* quality of match */) {
        if (res || haveVisited(ce)) {
          /*
          logln("ignore ", ce.valueType());
          if (res) logln("because already matched");
          else {
            foreach (i, t2; visited[0..visited_offs]) if (ce.valueType() == t2) {
              logln("because already visited - ", visited[0..visited_offs], "[", i, "]");
              break;
            }
          }*/
          return false;
        }
        addVisitor(ce.valueType());
        
        own_append(recurseInto, ce);
        own_append(scoredelta, newscore);
        
        auto backup = score_res?*score_res:0;
        if (score_res) *score_res = score + newscore;
        
        if (accept(ce)) {
          res = ce;
        } else
          if (score_res) *score_res = backup; // undo
        return true;
      });
      if (res) return res;
    }
    foreach (i, entry; recurseInto) {
      if (auto res = recurse(entry, score + scoredelta[i], score_res)) return res;
      if (mayFreeRejects) if (auto t = fastcast!(Temporary)(entry))
        own_append(cleanups, stuple(t, mayFreeRejects));
    }
    return null;
  }
  if (accept(ex)) return true;
  if (scorep) *scorep = 2;
  auto dcme = fastcast!(DontCastMeExpr) (ex);
  if (dcme) return false;
  if (auto res = recurse(ex, scorep?*scorep:0, scorep)) { ex = res; return true; }
  else return false;
}

bool gotImplicitCast(ref Expr ex, bool delegate(Expr) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, null, accept, mayFreeRejects, scorep);
}

bool gotImplicitCast(ref Expr ex, bool function(Expr) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, (Expr e) { return accept(e); }, mayFreeRejects, scorep);
}

bool gotImplicitCast(ref Expr ex, IType want, bool delegate(IType) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, want, (Expr ex) {
    return accept(ex.valueType());
  }, 2-mayFreeRejects, scorep);
}

bool gotImplicitCast(ref Expr ex, IType want, bool function(Expr) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, want, (Expr e) { return accept(e); }, mayFreeRejects, scorep);
}

bool gotImplicitCast(ref Expr ex, bool delegate(IType) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, null, (Expr ex) {
    return accept(ex.valueType());
  }, 2-mayFreeRejects, scorep);
}

bool gotImplicitCast(ref Expr ex, bool function(IType) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, (IType it) { return accept(it); }, mayFreeRejects, scorep);
}

Expr[] getAllImplicitCasts(Expr ex) {
  IType[] visited;
  bool haveVisited(Expr ex) {
    auto t1 = ex.valueType();
    foreach (t2; visited) if (t1 == t2) return true;
    return false;
  }
  Expr[] res;
  void recurse(Expr ex) {
    auto start = res.length;
    foreach (dg; implicits) {
      dg(ex, null, (Expr ce, int delta) {
        if (haveVisited(ce)) return false;
        own_append(visited, ce.valueType());
        own_append(res, ce);
        return true;
      });
    }
    foreach (entry; res[start .. $])
      recurse(entry);
  }
  auto dcme = fastcast!(DontCastMeExpr) (ex);
  own_append(res, ex);
  if (!dcme) recurse(ex);
  return res;
}

class IntLiteralAsShort : Expr {
  IntExpr ie;
  this(IntExpr ie) { this.ie = ie; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ie);
  mixin defaultCollapse!();
  override {
    IType valueType() { return Single!(Short); }
    string toString() { return Format("short:"[], ie); }
    void emitLLVM(LLVMFile lf) {
      push(lf, ie.num);
    }
  }
}

class IntLiteralAsByte : Expr {
  IntExpr ie;
  this(IntExpr ie) { this.ie = ie; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ie);
  mixin defaultCollapse!();
  override {
    IType valueType() { return Single!(Byte); }
    string toString() { return Format("byte:"[], ie); }
    void emitLLVM(LLVMFile lf) {
      push(lf, ie.num);
    }
  }
}

class ShortToIntCast_ : Expr {
  Expr sh;
  this(Expr sh) { this.sh = sh; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(sh);
  Expr collapse() {
    auto sh2 = .collapse(sh);
    if (auto ilas = fastcast!(IntLiteralAsShort) (sh2)) {
      return mkInt(cast(short) ilas.ie.num);
    }
    if (auto bsc = fastcast!(ByteToShortCast) (sh2)) {
      return new ByteToIntCast (bsc.b);
    }
    if (sh is sh2) return this;
    return fastalloc!(ShortToIntCast)(sh2);
  }
  override {
    IType valueType() { return Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "sext i16 ", save(lf, sh), " to i32");
    }
    string toString() { return Format("int:"[], sh); }
  }
}

final class ShortToIntCast : ShortToIntCast_ {
  static const isFinal = true;
  this(Expr sh) { super(sh); }
}

class UShortToIntCast_ : Expr {
  Expr ush;
  this(Expr ush) { this.ush = ush; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ush);
  mixin defaultCollapse!();
  override {
    IType valueType() { return Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "zext i16 ", save(lf, ush), " to i32");
    }
    string toString() { return Format("int:"[], ush); }
  }
}

final class UShortToIntCast : UShortToIntCast_ {
  static const isFinal = true;
  this(Expr ush) { super(ush); }
}

class ShortAsByte : Expr {
  Expr ex;
  this(Expr ex) { this.ex = ex; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  mixin defaultCollapse!();
  override {
    string toString() { return qformat("byte:", ex); }
    IType valueType() { return Single!(Byte); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "trunc i16 ", save(lf, ex), " to i8");
    }
  }
}

class ByteToShortCast : Expr {
  Expr b;
  bool signed;
  this(Expr b) {
    this.b = b;
    auto bt = resolveType(b.valueType());
    if (bt.llvmType() != "i8") {
      logln("Can't byte-to-short cast: wtf, "[], bt, " on "[], b);
      fail;
    }
    if (Single!(Byte) == bt) signed = true;
    else if (Single!(UByte) == bt || Single!(Char) == bt) signed = false;
    else { logln("!> ", bt); fail; }
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(b);
  override {
    Expr collapse() {
      // short: byte:short:5 -> short:(byte)5
      if (auto sab = fastcast!(ShortAsByte)(.collapse(b)))
        if (auto ilas = fastcast!(IntLiteralAsShort)(.collapse(sab.ex)))
          return fastalloc!(IntLiteralAsShort)(mkInt(cast(byte) ilas.ie.num));
      return this;
    }
    string toString() { return Format("short:"[], b); }
    IType valueType() { return Single!(Short); }
    void emitLLVM(LLVMFile lf) {
      if (signed) load(lf, "sext i8 ", save(lf, b), " to i16");
      else load(lf, "zext i8 ", save(lf, b), " to i16");
    }
  }
}

class ByteToIntCast : Expr {
  Expr b;
  bool signed;
  this(Expr b) {
    this.b = b;
    auto bt = resolveType(b.valueType());
    if (bt.llvmType() != "i8") {
      logln("Can't byte-to-int cast: wtf, "[], bt, " on "[], b);
      fail;
    }
    if (Single!(Byte) == bt) signed = true;
    else if (Single!(UByte) == bt || Single!(Char) == bt) signed = false;
    else { logln("!> ", bt); fail; }
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(b);
  Expr collapse() {
    if (auto ilab = fastcast!(IntLiteralAsByte)(.collapse(b))) {
      return ilab.ie;
    }
    if (auto rce = fastcast!(RCE)(.collapse(b))) {
      if (auto ilab = fastcast!(IntLiteralAsByte)(.collapse(rce.from))) {
        return ilab.ie;
      }
    }
    return this;
  }
  override {
    string toString() { return Format("int:"[], b); }
    IType valueType() { return Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      if (signed) load(lf, "sext i8 ", save(lf, b), " to i32");
      else load(lf, "zext i8 ", save(lf, b), " to i32");
    }
  }
}

Expr reinterpret_cast(IType to, Expr from) {
  if (auto lv = fastcast!(LValue) (from))
    return fastalloc!(RCL)(to, lv);
  if (auto cv = fastcast!(CValue) (from))
    return fastalloc!(RCC)(to, cv);
  if (auto mv = fastcast!(MValue) (from))
    return fastalloc!(RCM)(to, mv);
  return fastalloc!(RCE)(to, from);
}

// don't allow write access
Expr reinterpret_cast_safe(IType to, Expr from) {
  if (auto cv = fastcast!(CValue) (from))
    return fastalloc!(RCC)(to, cv);
  return fastalloc!(RCE)(to, from);
}

import std.moduleinit;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto tp = ex.valueType().proxyType();
    if (!tp) return null;
    return reinterpret_cast(resolveType(tp), ex);
  };
  implicits ~= delegate Expr(Expr ex) {
    auto evt = ex.valueType();
    if (Single!(Byte) == evt || Single!(Char) == evt || Single!(UByte) == evt)
      return fastalloc!(ByteToShortCast)(ex);
    else
      return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(Short) == ex.valueType())
      return fastalloc!(ShortToIntCast)(ex);
    else
      return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(UShort) == ex.valueType())
      return fastalloc!(UShortToIntCast)(ex);
    else
      return null;
  };
  implicits ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Byte) != ex.valueType() && Single!(UByte) != ex.valueType()) return null;
    return reinterpret_cast(Single!(Char), ex); // concession to C libs
  };
  // teh hax :D
  foreach (m; ModuleInfo.modules())
    if (m.name == "ast.casting"[]) {
      m.localClasses ~= RCE.classinfo;
      m.localClasses ~= RCL.classinfo;
      m.localClasses ~= RCM.classinfo;
      m.localClasses ~= RCC.classinfo;
    }
}
