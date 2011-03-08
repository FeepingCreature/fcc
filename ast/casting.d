module ast.casting;

import ast.base, ast.parse;

class RC {
  Expr from;
  IType to;
}

template ReinterpretCast_Contents(T) {
  this(IType to, T from) {
    this.from = from;
    this.to = to;
    static if (is(T==Expr)) {
      if (fastcast!(LValue)~ from || fastcast!(CValue)~ from) {
        logln(this, "? Suure? ");
        asm { int 3; }
      }
    }
    // if (to.size != from.valueType().size) asm { int 3; }
    if (to.size != from.valueType().size) {
      logln("Can't cast ", from, " to ", to, "; ", from.valueType(), " size ", from.valueType().size, " vs. ", to.size, "!");
      fail();
    }
  }
  private this() { }
  typeof(this) dup() { return new typeof(this)(to, fastcast!(T) (from.dup)); }
  mixin defaultIterate!(from);
  override {
    static if (is(typeof((fastcast!(T)~ from).emitLocation(null))))
      void emitLocation(AsmFile af) {
        (fastcast!(T)~ from).emitLocation(af);
      }
    static if (is(typeof((fastcast!(T)~ from).emitAssignment(null))))
      void emitAssignment(AsmFile af) {
        (fastcast!(T)~ from).emitAssignment(af);
      }
  }
}

template ReinterpretCast(T) {
  static if (is(T==Expr)) {
    class ReinterpretCast : RC, Expr, HasInfo {
      mixin ReinterpretCast_Contents!(Expr);
      override {
        string toString() { return Format("(", to, ": ", from, ")"); }
        IType valueType() { return to; }
        string getInfo() { return Format(to, ":"); }
        void emitAsm(AsmFile af) {
          _reinterpret_cast_expr(this, af);
        }
      }
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
extern(C) void _reinterpret_cast_expr(RCE, AsmFile);

import ast.fold;
static this() {
  foldopt ~= delegate Expr(Expr ex) {
    if (auto rce1 = fastcast!(RCE)~ ex) {
      if (auto rce2 = fastcast!(RCE)~ fold(rce1.from)) {
        return foldex(reinterpret_cast(rce1.to, foldex(rce2.from)));
      }
    }
    return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto rce = fastcast!(RCE)~ ex) {
      if (rce.from.valueType() == rce.to)
        return foldex(rce.from);
    }
    return null;
  };
}

// casts to types that'd be implicit-converted anyway
Object gotExplicitDefaultCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  IType dest;
  if (!rest(t2, "type", &dest) || !t2.accept(":"))
    return null;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex) || !gotImplicitCast(ex, (IType it) { return test(it == dest); }))
    return null;
  
  // confirm
  if (ex.valueType() != dest) return null;
  
  text = t2;
  return fastcast!(Object)~ reinterpret_cast(dest, ex);
}
mixin DefaultParser!(gotExplicitDefaultCastExpr, "tree.expr.cast_explicit_default", "701");

// IType parameter is just advisory!
// Functions may ignore it.
Expr delegate(Expr, IType)[] converts;

// casts to types that have conversion defined
Object gotConversionCast(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType dest;
  if (!rest(t2, "type", &dest) || !t2.accept(":"))
    return null;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Unable to parse cast source");
  Expr res;
  foreach (dg; converts) {
    auto ex2 = dg(ex, dest);
    if (ex2 && ex2.valueType() == dest) {
      res = ex2;
      break;
    }
  }
  if (res) text = t2;
  return fastcast!(Object)~ res;
}
mixin DefaultParser!(gotConversionCast, "tree.expr.cast_convert", "702");

Object gotCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  IType dest;
  if (!rest(t2, "type", &dest) || !t2.accept(":"))
    return null;
  IType[] types;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex) || !gotImplicitCast(ex, (IType it) { types ~= it; return it.size == dest.size; }))
    t2.failparse(
      "Expression not matched in cast; none of ", types, " matched ", dest.size, ". "
    );
    // return null;
  
  text = t2;
  return fastcast!(Object)~ reinterpret_cast(dest, ex);
}
mixin DefaultParser!(gotCastExpr, "tree.expr.cast", "7");

import tools.base: toDg;

// implicit conversions
struct implicits { static {
  void delegate(Expr, IType, void delegate(Expr))[] dgs;
  void opCatAssign(void delegate(Expr, IType, void delegate(Expr)) dg) {
    dgs ~= dg;
  }
  void opCatAssign(void delegate(Expr, void delegate(Expr)) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, void delegate(Expr) dg2) {
      dg(ex, dg2);
    };
  }
  void opCatAssign(Expr delegate(Expr) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, void delegate(Expr) dg2) {
      if (auto res = dg(ex)) dg2(res);
    };
  }
  void opCatAssign(Expr delegate(Expr, IType) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, IType it, void delegate(Expr) dg2) {
      if (auto res = dg(ex, it)) dg2(res);
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
    void emitAsm(AsmFile af) { sup.emitAsm(af); }
    string toString() { return Format("__dcm(", sup, ")"); }
  }
}

class DontCastMeCValue : DontCastMeExpr, CValue {
  this(CValue cv) { super(cv); }
  typeof(this) dup() { return new typeof(this)(fastcast!(CValue)~ sup); }
  override void emitLocation(AsmFile af) { (fastcast!(CValue)~ sup).emitLocation(af); }
}

class DontCastMeLValue : DontCastMeCValue, LValue {
  this(LValue lv) { super(lv); }
  typeof(this) dup() { return new typeof(this)(fastcast!(LValue)~ sup); }
}

Expr dcm(Expr ex) {
  if (auto lv = fastcast!(LValue)~ ex) return new DontCastMeLValue(lv);
  else if (auto cv = fastcast!(CValue)~ ex) return new DontCastMeCValue(cv);
  else return new DontCastMeExpr(ex);
}

Object gotDCMExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (t2.accept("__dcm(") && rest(t2, "tree.expr", &ex) && t2.accept(")")) {
    text = t2;
    return new DontCastMeExpr(ex);
  } else return null;
}
mixin DefaultParser!(gotDCMExpr, "tree.expr.dcm", "53");

import tools.threads: TLS;
import ast.namespace;
TLS!(IType[]) gotImplicitCast_visited_cache; // we go in here a lot, so this pays off
static this() { New(gotImplicitCast_visited_cache, { return &(new Stuple!(IType[]))._0; }); }
bool gotImplicitCast(ref Expr ex, IType want, bool delegate(Expr) accept) {
  if (!ex) asm { int 3; }
  auto ns = namespace();
  if (!ns) namespace.set(new NoNameSpace); // lots of stuff does namespace().get!() .. pacify it
  scope(exit) namespace.set(ns);
  auto visited = *(gotImplicitCast_visited_cache.ptr());
  scope(exit) *(gotImplicitCast_visited_cache.ptr()) = visited;
  int visited_offs;
  void addVisitor(IType it) {
    if (visited_offs < visited.length)
      visited[visited_offs++] = it;
    else { visited ~= it; visited_offs ++; }
  }
  want = resolveType(want);
  bool haveVisited(Expr ex) {
    auto t1 = ex.valueType();
    foreach (t2; visited[0 .. visited_offs]) if (t1 == t2) return true;
    return false;
  }
  Expr recurse(Expr ex) {
    Expr[] recurseInto;
    foreach (dg; implicits) {
      Expr res;
      dg(ex, want, (Expr ce) {
        if (res || haveVisited(ce)) return;
        addVisitor(ce.valueType());
        if (accept(ce)) res = ce;
        recurseInto ~= ce;
      });
      if (res) return res;
    }
    foreach (entry; recurseInto)
      if (auto res = recurse(entry)) return res;
    return null;
  }
  auto dcme = fastcast!(DontCastMeExpr) (ex);
  if (accept(ex)) return true;
  if (dcme) return false;
  if (auto res = recurse(ex)) { ex = res; return true; }
  else return false;
}

bool gotImplicitCast(ref Expr ex, bool delegate(Expr) accept) {
  return gotImplicitCast(ex, null, accept);
}

void resolveExpr(ref Expr ex) {
  auto et = ex.valueType();
  auto re = resolveType(et);
  if (re is et) return;
  ex = reinterpret_cast(re, ex);
}

bool gotImplicitCast(ref Expr ex, IType want, bool delegate(IType) accept) {
  return gotImplicitCast(ex, want, (Expr ex) {
    return accept(resolveType(ex.valueType()));
  }) && (resolveExpr(ex), true);
}

bool gotImplicitCast(ref Expr ex, bool delegate(IType) accept) {
  return gotImplicitCast(ex, null, (Expr ex) {
    return accept(resolveType(ex.valueType()));
  }) && (resolveExpr(ex), true);
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
      dg(ex, null, (Expr ce) {
        if (haveVisited(ce)) return;
        visited ~= ce.valueType();
        res ~= ce;
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

class ShortToIntCast : Expr {
  Expr sh;
  this(Expr sh) { this.sh = sh; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    IType valueType() { return Single!(SysInt); }
    void emitAsm(AsmFile af) {
      sh.emitAsm(af);
      af.comment("short to int cast");
      af.put("xorl %eax, %eax");
      af.popStack("%ax", sh.valueType());
      af.pushStack("%eax", valueType());
    }
  }
}

class ByteToShortCast : Expr {
  Expr b;
  this(Expr b) { this.b = b; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    IType valueType() { return Single!(Short); }
    void emitAsm(AsmFile af) {
      b.emitAsm(af);
      // lol.
      af.comment("byte to short cast lol");
      af.put("xorw %ax, %ax");
      af.popStack("%al", b.valueType());
      af.pushStack("%ax", valueType());
    }
  }
}

Expr reinterpret_cast(IType to, Expr from) {
  if (auto lv = fastcast!(LValue)~ from)
    return new RCL(to, lv);
  if (auto cv = fastcast!(CValue)~ from)
    return new RCC(to, cv);
  if (auto mv = fastcast!(MValue)~ from)
    return new RCM(to, mv);
  return new RCE(to, from);
}

import std.moduleinit;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto tp = fastcast!(TypeProxy)~ ex.valueType();
    if (!tp) return null;
    return reinterpret_cast(resolveType(fastcast!(IType)~ tp), ex);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (ex.valueType() == Single!(Byte) || ex.valueType() == Single!(Char))
      return new ByteToShortCast(ex);
    else
      return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (ex.valueType() == Single!(Short))
      return new ShortToIntCast(ex);
    else
      return null;
  };
  // teh hax :D
  foreach (m; ModuleInfo.modules())
    if (m.name == "ast.casting") {
      m.localClasses ~= RCE.classinfo;
      m.localClasses ~= RCL.classinfo;
      m.localClasses ~= RCM.classinfo;
      m.localClasses ~= RCC.classinfo;
    }
}
