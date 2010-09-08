module ast.casting;

import ast.base, ast.parse;

class ReinterpretCast(T) : T {
  T from; IType to;
  this(IType to, T from) {
    this.from = from;
    this.to = to;
    // if (to.size != from.valueType().size) asm { int 3; }
    assert(to.size == from.valueType().size, Format("Can't cast ", from, " to ", to, "; ", from.valueType().size, " vs. ", to.size, "!"));
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(from);
  override {
    string toString() { return Format("reinterpret_cast<", to, "> ", from); }
    IType valueType() { return to; }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("to.size"));
      from.emitAsm(af);
    }
    static if (is(typeof(&from.emitLocation)))
      void emitLocation(AsmFile af) {
        from.emitLocation(af);
      }
  }
}
alias ReinterpretCast!(Expr) RCE;
alias ReinterpretCast!(LValue) RCL;

static this() {
  foldopt ~= delegate Expr(Expr ex) {
    if (auto rce1 = cast(RCE) ex) {
      if (auto rce2 = cast(RCE) rce1.from) {
        return new RCE(rce1.to, rce2.from);
      }
    }
    return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto rce = cast(RCE) ex) {
      if (rce.from.valueType() == rce.to)
        return rce.from;
    }
    return null;
  };
}

// casts to types that'd be implicit-converted anyway
Object gotExplicitDefaultCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!t2.accept("cast(")) return null;
  IType dest;
  if (!rest(t2, "type", &dest))
    throw new Exception("No type matched in cast expression: "~t2.next_text());
  if (!t2.accept(")"))
    throw new Exception("Missed closing bracket in cast at "~t2.next_text());
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex) || !gotImplicitCast(ex, (IType it) { return test(it == dest); }))
    return null;
  
  // confirm
  if (ex.valueType() != dest) return null;
  
  text = t2;
  return cast(Object) new RCE(dest, ex);
}
mixin DefaultParser!(gotExplicitDefaultCastExpr, "tree.expr.cast_explicit_default", "701");

// casts to types that have conversion defined
Object gotConversionCast(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!t2.accept("cast(")) return null;
  IType dest;
  if (!rest(t2, "type", &dest))
    throw new Exception("No type matched in cast expression: "~t2.next_text());
  if (!t2.accept(")"))
    throw new Exception("Missed closing bracket in cast at "~t2.next_text());
  char* longest;
  if (!rest(t2, "tree.convert", &ex, (Expr ex) {
    return !!(ex.valueType() == dest);
  }))
    return null;
  
  text = t2;
  // override type
  return cast(Object) new RCE(dest, ex);
}
mixin DefaultParser!(gotConversionCast, "tree.expr.cast_convert", "702");

Object gotCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (t2.accept("cast(")) {
    IType dest;
    if (!rest(t2, "type", &dest))
      throw new Exception("No type matched in cast expression: "~t2.next_text());
    if (!t2.accept(")"))
      throw new Exception("Missed closing bracket in cast at "~t2.next_text());
    if (!rest(t2, "tree.expr _tree.expr.arith", &ex, (Expr ex) { return ex.valueType().size == dest.size; }))
      return null;
      // throw new Exception("Expression not matched in cast: "~t2.next_text());
    
    text = t2;
    return new ReinterpretCast!(Expr)(dest, ex);
  } else return null;
}
mixin DefaultParser!(gotCastExpr, "tree.expr.cast", "7");

import tools.base: toDg;

// implicit conversions
struct implicits { static {
  void delegate(Expr, void delegate(Expr))[] dgs;
  void opCatAssign(void delegate(Expr, void delegate(Expr)) dg) {
    dgs ~= dg;
  }
  void opCatAssign(Expr delegate(Expr) dg) {
    dgs ~= dg /apply/ function void(typeof(dg) dg, Expr ex, void delegate(Expr) dg2) {
      if (auto res = dg(ex)) dg2(res);
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

Object gotDCMExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (t2.accept("__dcm(") && rest(t2, "tree.expr", &ex) && t2.accept(")")) {
    text = t2;
    return new DontCastMeExpr(ex);
  } else return null;
}
mixin DefaultParser!(gotDCMExpr, "tree.expr.dcm", "53");

bool gotImplicitCast(ref Expr ex, bool delegate(Expr) accept) {
  IType[] visited;
  bool haveVisited(Expr ex) {
    auto t1 = ex.valueType();
    foreach (t2; visited) if (t1 == t2) return true;
    return false;
  }
  Expr recurse(Expr ex) {
    Expr[] recurseInto;
    foreach (dg; implicits) {
      Expr res;
      dg(ex, (Expr ce) {
        if (res || haveVisited(ce)) return;
        visited ~= ce.valueType();
        if (accept(ce)) res = ce;
        recurseInto ~= ce;
      });
      if (res) return res;
    }
    foreach (entry; recurseInto)
      if (auto res = recurse(entry)) return res;
    return null;
  }
  auto dcme = cast(DontCastMeExpr) ex;
  if (accept(ex)) return true;
  if (dcme) return false;
  if (auto res = recurse(ex)) { ex = res; return true; }
  else return false;
}

bool gotImplicitCast(ref Expr ex, bool delegate(IType) accept) {
  return gotImplicitCast(ex, (Expr ex) { return accept(ex.valueType()); });
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

class CharToShortCast : Expr {
  Expr sh;
  this(Expr sh) { this.sh = sh; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    IType valueType() { return Single!(Short); }
    void emitAsm(AsmFile af) {
      sh.emitAsm(af);
      // lol.
      af.comment("byte to short cast lol");
      af.put("xorw %ax, %ax");
      af.popStack("%al", sh.valueType());
      af.pushStack("%ax", valueType());
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (ex.valueType() == Single!(Char))
      return new CharToShortCast(ex);
    else
      return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (ex.valueType() == Single!(Short))
      return new ShortToIntCast(ex);
    else
      return null;
  };
}
