module ast.pointer;

import ast.types, ast.base, parseBase, tools.base: This, This_fn, rmSpace;

class Pointer : Type {
  IType target;
  this(IType t) { target = t; }
  override {
    int opEquals(IType ty) {
      ty = resolveType(ty);
      if (!super.opEquals(ty)) return false;
      auto p = fastcast!(Pointer)~ ty;
      return target == p.target;
    }
    int size() { return nativePtrSize; }
    string mangle() { return "ptrto_"~target.mangle(); }
    string toString() { return Format(target, "*"); }
  }
}

alias Single!(Pointer, Single!(Void)) voidp;

// &foo
class RefExpr : Expr {
  CValue src;
  this(CValue cv) { assert(!!cv); this.src = cv; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(src);
  override {
    IType valueType() {
      return new Pointer(src.valueType());
    }
    void emitAsm(AsmFile af) {
      src.emitLocation(af);
    }
    string toString() {
      return Format("&", src);
    }
  }
}

// *foo
class DerefExpr : LValue {
  Expr src;
  this(Expr ex) {
    src = ex;
    if (!fastcast!(Pointer) (resolveType(src.valueType())))
      throw new Exception(Format("Can't dereference non-pointer: ", src));
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(src);
  override {
    IType valueType() {
      return fastcast!(Pointer) (resolveType(src.valueType())).target;
    }
    void emitAsm(AsmFile af) {
      src.emitAsm(af);
      af.popStack("%eax", src.valueType());
      af.pushStack("(%eax)", valueType());
    }
    void emitLocation(AsmFile af) {
      src.emitAsm(af);
    }
  }
  string toString() { return Format("*", src); }
}

bool isVoidP(IType it) {
  if (!it) return false;
  auto p = fastcast!(Pointer)~ it;
  if (!p) return false;
  return !!fastcast!(Void) (p.target);
}

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    if (text.accept("*")) { return new Pointer(cur); }
    else return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto re = fastcast!(RefExpr) (ex)) {
      if (auto de = fastcast!(DerefExpr) (re.src)) {
        return de.src;
      }
    }
    return null;
  };
  // Pointers must NOT autocast to void* unless expected!
  implicits ~= delegate Expr(Expr ex, IType target) {
    if (!target) return null;
    if (auto p = fastcast!(Pointer) (resolveType(ex.valueType()))) {
      if (!isVoidP(p) && isVoidP(target)) {
        return dcm(reinterpret_cast(voidp, ex));
      }
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isVoidP(ex.valueType()) && fastcast!(Pointer) (resolveType(expect))) {
      return reinterpret_cast(expect, ex);
    }
    return null;
  };
}

import ast.fold, ast.casting;
Object gotRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex)) {
    text.setError("Address operator found but nothing to take address matched");
    return null;
  }
  
  IType[] tried;
  if (!gotImplicitCast(ex, (Expr ex) {
    auto f = foldex(ex);
    tried ~= f.valueType();
    return test(fastcast!(CValue)~ f);
  })) {
    text.setError("Can't take reference: ", ex,
    " does not become a cvalue (", tried, ")");
    return null;
  }
  
  text = t2;
  auto cv = fastcast!(CValue)~ fold(ex);
  assert(!!cv);
  
  return new RefExpr(cv);
}
mixin DefaultParser!(gotRefExpr, "tree.expr.ref", "21", "&");

Object gotDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Dereference operator found but no expression matched");
  
  if (!gotImplicitCast(ex, (IType it) { return !!fastcast!(Pointer) (it); })) {
    return null;
  }
  text = t2;
  return new DerefExpr(ex);
}
mixin DefaultParser!(gotDerefExpr, "tree.expr.deref", "22", "*");

class Symbol : Expr {
  string name;
  this(string name) { this.name = name; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override IType valueType() { return voidp; }
  override void emitAsm(AsmFile af) {
    af.pushStack("$"~name, valueType());
  }
}

// fill string at emitAsm-time via dg
class LateSymbol : Expr {
  void delegate(AsmFile) dg;
  string* name;
  this(void delegate(AsmFile) dg, string* name) { this.dg = dg; this.name = name; }
  private this() { }
  LateSymbol dup() { return new LateSymbol(dg, name); }
  mixin defaultIterate!();
  override IType valueType() { return voidp; }
  override void emitAsm(AsmFile af) {
    if (!*name) dg(af);
    af.pushStack("$"~*name, valueType());
  }
}
