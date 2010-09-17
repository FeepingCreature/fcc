module ast.pointer;

import ast.types, ast.base, parseBase, tools.base: This, This_fn, rmSpace;

class Pointer : Type {
  IType target;
  this(IType t) { target = t; }
  override {
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      auto p = cast(Pointer) ty;
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
  this(CValue cv) { assert(cv); this.src = cv; }
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
    if (!cast(Pointer) src.valueType())
      throw new Exception(Format("Can't dereference non-pointer: ", src));
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(src);
  override {
    IType valueType() {
      return (cast(Pointer) src.valueType()).target;
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

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    if (text.accept("*")) { return new Pointer(cur); }
    else return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto re = cast(RefExpr) ex) {
      if (auto de = cast(DerefExpr) re.src) {
        return de.src;
      }
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (auto p = cast(Pointer) ex.valueType()) {
      if (p.target != Single!(Void))
        return reinterpret_cast(voidp, ex);
    }
    return null;
  };
}

import ast.fold, ast.casting;
Object gotRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("&")) return null;
  
  Expr ex;
  if (!rest(text, "tree.expr _tree.expr.arith", &ex)) {
    error = "Address operator found but nothing to take address matched at '"~text.next_text()~"'";
    return null;
  }
  
  if (!gotImplicitCast(ex, (Expr ex) {
    return test(cast(CValue) fold(ex));
  })) throw new Exception(Format("Can't take reference: ", ex, " does not become a cvalue at ", text.next_text()));
  
  auto cv = cast(CValue) fold(ex);
  assert(!!cv);
  
  return new RefExpr(cv);
}
mixin DefaultParser!(gotRefExpr, "tree.expr.ref", "21");

Object gotDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("*")) return null;
  
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    throw new Exception("Dereference operator found but no expression matched at '"~text.next_text()~"'");
  
  if (!gotImplicitCast(ex, (IType it) { return !!cast(Pointer) it; })) {
    return null;
  }
  text = t2;
  return new DerefExpr(ex);
}
mixin DefaultParser!(gotDerefExpr, "tree.expr.deref", "22");

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
