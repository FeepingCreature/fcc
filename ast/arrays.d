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

import ast.parse, ast.literals;
Object gotSALength(ref string text, ParseCb cont, ParseCb rest) {
  auto lhs = lhs_partial(), le = cast(Expr) lhs;
  if (!le) return null;
  
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = cast(StaticArray) ex.valueType()) {
      if (!text.accept(".length")) return null;
      return new IntExpr(sa.length);
    } else return null;
  };
}
mixin DefaultParser!(gotSALength, "tree.rhs_partial.static_array_length");
