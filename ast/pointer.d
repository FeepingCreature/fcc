module ast.pointer;

import ast.types, ast.base;

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

static this() {
  typeModlist ~= delegate Type(ref string text, Type cur) {
    if (text.accept("*")) { return new Pointer(cur); }
    else return null;
  };
}
