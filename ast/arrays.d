module ast.arrays;

import ast.base, ast.types, tools.base: This, This_fn, rmSpace;

class StaticArray : Type {
  Type elemType;
  int length;
  this() { }
  mixin This!("elemType, length");
  override int size() {
    return length * elemType.size();
  }
  override string mangle() {
    return Format("Static_", length, "_of_", elemType.mangle());
  }
}

static this() {
  typeModlist ~= delegate Type(ref string text, Type cur) {
    auto t2 = text;
    StaticArray res;
    if (t2.accept("[") && (New(res), res.elemType = cur, true) &&
        t2.gotInt(res.length) &&
        t2.accept("]")
      )
    {
      text = t2;
      return res;
    } else return null;
  };
}
