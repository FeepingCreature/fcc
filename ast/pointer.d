module ast.pointer;

import ast.types, ast.base, parseBase, tools.base: This, This_fn, rmSpace;

class Pointer : Type {
  IType target;
  this(IType t) { target = t; }
  int opEquals(Object obj) {
    if (obj.classinfo !is this.classinfo) return false;
    auto p = cast(Pointer) cast(void*) obj;
    return cast(Object) target == cast(Object) p.target;
  }
  override {
    int size() { return nativePtrSize; }
    string mangle() { return "ptrto_"~target.mangle(); }
    string toString() { return Format(target, "*"); }
  }
}

// &foo
class RefExpr : Expr {
  CValue src;
  mixin This!("src");
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
  mixin defaultIterate!(src);
  override {
    IType valueType() {
      return (cast(Pointer) src.valueType()).target;
    }
    void emitAsm(AsmFile af) {
      src.emitAsm(af);
      af.popStack("%eax", src.valueType());
      assert(valueType().size == 4, "Weird dereference: "~(cast(Object) valueType()).toString); // TODO: multi-step push
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
}

Object gotRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("&")) return null;
  
  Expr ex;
  if (!rest(text, "tree.expr >tree.expr.arith", &ex))
    throw new Exception("Address operator found but nothing to take address matched at '"~text.next_text()~"'");
  
  auto cv = cast(CValue) ex;
  if (!cv) throw new Exception(Format("Can't take reference: ", ex, " not an lvalue at ", text.next_text()));
  
  return new RefExpr(cv);
}
mixin DefaultParser!(gotRefExpr, "tree.expr.ref", "21");

Object gotDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("*")) return null;
  
  Expr ex;
  if (!rest(text, "tree.expr >tree.expr.arith", &ex))
    throw new Exception("Dereference operator found but no expression matched at '"~text.next_text()~"'");
  
  return new DerefExpr(ex);
}
mixin DefaultParser!(gotDerefExpr, "tree.expr.deref", "22");
