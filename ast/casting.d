module ast.casting;

import ast.base, ast.parse;

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
    auto new_from_test = fastcast!(T) (from);
    if (!new_from_test/* || from.valueType().size != backup.valueType().size*/) {
      // Liskov, if already deceased, is getting quite a spin here.
      logln("Missubstitution!"[]);
      logln("In cast of "[], T.stringof);
      logln("Was: "[], backup, " ", backup.valueType());
      logln(" To: "[], from, " ", from.valueType());
      fail;
    }
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

import ast.fold;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto rce = fastcast!(RCE) (it)) {
      if (exactlyEquals(rce.from.valueType(), rce.to))
        return rce.from;
      
      if (auto rce2 = fastcast!(RCE) (rce.from)) {
        return reinterpret_cast(rce.to, rce2.from);
      }
    }
    return null;
  };
}

// casts to types that'd be implicit-converted anyway
Object gotExplicitDefaultCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  IType dest;
  if (!rest(t2, "type"[], &dest) || !t2.accept(":"[]))
    return null;
  if (t2.accept(":"[])) return null;
  dest = forcedConvert(dest);
  try {
    if (!rest(t2, "tree.expr _tree.expr.arith"[], &ex) || !gotImplicitCast(ex, dest, (IType it) { return test(it == dest); })) {
      if (!ex)
        t2.failparse("Cannot parse cast source");
      // t2.setError("can't get "[], ex.valueType(), " into "[], dest);
      t2.setError("types don't match in explicit-cast: ", ex.valueType(), " into ", dest);
      return null;
    }
  } catch (Exception ex) {
    t2.failparse(ex);
  }
  
  // confirm
  if (ex.valueType() != dest) return null;
  
  text = t2;
  return fastcast!(Object)~ reinterpret_cast(dest, ex);
}
mixin DefaultParser!(gotExplicitDefaultCastExpr, "tree.expr.cast_explicit_default"[], "241801"[]);

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

// casts to types that have conversion defined
Object gotConversionCast(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType dest;
  if (!rest(t2, "type"[], &dest) || !t2.accept(":"[]))
    return null;
  if (t2.accept(":"[])) return null;
  dest = forcedConvert(dest);
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith"[], &ex)) {
    t2.setError("Unable to parse cast source"[]);
    return null;
  }
  ex = forcedConvert(ex);
  Expr res = tryConvert(ex, dest);
  if (res) text = t2;
  return fastcast!(Object)~ res;
}
mixin DefaultParser!(gotConversionCast, "tree.expr.cast_convert"[], "241802"[]);

Object gotCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  IType dest;
  if (!rest(t2, "type"[], &dest) || !t2.accept(":"[]))
    return null;
  if (t2.accept(":"[])) return null;
  dest = forcedConvert(dest);
  IType[] types;
  if (!rest(t2, "tree.expr _tree.expr.arith"[], &ex)) {
    t2.failparse("Failed to get expression"[]);
  }
  if (!gotImplicitCast(ex, dest, (IType it) { types ~= it; return it.llvmSize() == dest.llvmSize(); })) {
    t2.setError("Expression not matched in cast; none of "[], types, " matched "[], dest.llvmSize(), ". "[]);
    return null;
  }
  
  text = t2;
  resetError;
  return fastcast!(Object)~ reinterpret_cast(dest, ex);
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
  if (scorep) *scorep = 2;
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
    else { visited ~= it; visited_offs ++; }
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
        recurseInto ~= ce;
        scoredelta ~= newscore;
        if (accept(ce)) {
          res = ce;
          if (score_res) *score_res = score + newscore;
        }
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
  auto dcme = fastcast!(DontCastMeExpr) (ex);
  if (dcme) return false;
  if (auto res = recurse(ex, 0, scorep)) { ex = res; return true; }
  else return false;
}

bool gotImplicitCast(ref Expr ex, bool delegate(Expr) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, null, accept, mayFreeRejects, scorep);
}

bool gotImplicitCast(ref Expr ex, IType want, bool delegate(IType) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, want, (Expr ex) {
    return accept(ex.valueType());
  }, 2-mayFreeRejects, scorep);
}

bool gotImplicitCast(ref Expr ex, bool delegate(IType) accept, bool mayFreeRejects = true, int* scorep = null) {
  return gotImplicitCast(ex, null, (Expr ex) {
    return accept(ex.valueType());
  }, 2-mayFreeRejects, scorep);
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
        visited ~= ce.valueType();
        res ~= ce;
        return true;
      });
    }
    foreach (entry; res[start .. $])
      recurse(entry);
  }
  auto dcme = fastcast!(DontCastMeExpr) (ex);
  res ~= ex;
  if (!dcme) recurse(ex);
  return res;
}

class ShortToIntCast_ : Expr {
  Expr sh;
  this(Expr sh) { this.sh = sh; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(sh);
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
  foldopt ~= delegate Itr(Itr it) {
    if (auto sic = fastcast!(ShortToIntCast) (it)) {
      if (auto bsc = fastcast!(ByteToShortCast) (sic.sh)) {
        return new ByteToIntCast (bsc.b);
      }
    }
    return null;
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
