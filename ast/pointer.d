module ast.pointer;

import ast.types, ast.base, parseBase, tools.base: This, This_fn, rmSpace;

class Pointer : Type {
  Type target;
  this(Type t) { target = t; }
  int opEquals(Object obj) {
    if (obj.classinfo !is this.classinfo) return false;
    auto p = cast(Pointer) cast(void*) obj;
    return target == p.target;
  }
  override int size() { return nativePtrSize; }
  override string mangle() { return "ptrto_"~target.mangle(); }
}

// &foo
class RefExpr : Expr {
  CValue src;
  mixin This!("src");
  override {
    Type valueType() {
      return new Pointer(src.valueType());
    }
    void emitAsm(AsmFile af) {
      src.emitLocation(af);
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
  override {
    Type valueType() {
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
}

static this() {
  typeModlist ~= delegate Type(ref string text, Type cur) {
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
