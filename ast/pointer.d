module ast.pointer;

import ast.types, ast.base, tools.base: This, This_fn, rmSpace;

class Pointer : Type {
  Type target;
  this(Type t) { target = t; size = nativePtrSize; }
  int opEquals(Object obj) {
    if (obj.classinfo !is this.classinfo) return false;
    auto p = cast(Pointer) cast(void*) obj;
    return target == p.target;
  }
  override string mangle() { return "ptrto_"~target.mangle(); }
}

// &foo
class RefExpr : Expr {
  LValue src;
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
      assert(valueType().size == 4); // TODO: multi-step push
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
