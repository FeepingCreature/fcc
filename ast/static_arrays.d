module ast.static_arrays;

import ast.base, ast.types;

class StaticArray : Type {
  IType elemType;
  int length;
  this() { }
  this(IType et, int len) { elemType = et; length = len; }
  override int size() {
    return length * elemType.size();
  }
  override string mangle() {
    return Format("Static_", length, "_of_", elemType.mangle());
  }
  override int opEquals(Object obj) {
    return super.opEquals(obj) &&
      (cast(StaticArray) obj).elemType == cast(Object) elemType &&
      (cast(StaticArray) obj).length == length;
  }
}

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    auto t2 = text;
    int len;
    if (t2.accept("[") &&
        t2.gotInt(len) &&
        t2.accept("]")
      )
    {
      text = t2;
      return new StaticArray(cur, len);
    } else return null;
  };
}

import ast.parse, ast.int_literal;
Object gotSALength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = cast(StaticArray) ex.valueType()) {
      if (!text.accept(".length")) return null;
      return new IntExpr(sa.length);
    } else return null;
  };
}
mixin DefaultParser!(gotSALength, "tree.rhs_partial.static_array_length");

// static array literal
class DataExpr : Expr {
  ubyte[] data;
  this(ubyte[] ub) { data = ub; }
  mixin defaultIterate!();
  override IType valueType() { return new StaticArray(Single!(Char), data.length); }
  override void emitAsm(AsmFile af) {
    auto d2 = data;
    while (d2.length >= 4) {
      auto i = (cast(int[]) d2.take(4))[0];
      af.pushStack(Format("$", i), Single!(SysInt)); // TODO: use 4-byte type
    }
    while (d2.length) {
      auto c = d2.take();
      af.pushStack(Format("$", c), Single!(Char));
    }
  }
}
