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
  override int opEquals(IType ty) {
    return super.opEquals(ty) &&
      ((cast(StaticArray) ty).elemType == elemType) &&
      ((cast(StaticArray) ty).length == length);
  }
}

import ast.fold;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb cont, ParseCb rest) {
    auto t2 = text;
    Expr len_ex;
    if (t2.accept("[") &&
        rest(t2, "tree.expr", &len_ex) &&
        t2.accept("]")
      )
    {
      text = t2;
      auto len = fold(len_ex);
      if (auto ie = cast(IntExpr) len) 
        return new StaticArray(cur, ie.num);
      throw new Exception(Format("Not a constant: ", len));
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

Expr getSAPtr(Expr sa) {
  auto vt = cast(StaticArray) sa.valueType();
  return new ReinterpretCast!(Expr) (new Pointer(vt.elemType), new RefExpr(cast(CValue) sa));
}

import ast.parse, ast.namespace, ast.int_literal, ast.pointer, ast.casting;
Object gotSAPointer(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = cast(StaticArray) ex.valueType()) {
      if (!text.accept(".ptr")) return null;
      auto cv = cast(CValue) ex;
      if (!cv) throw new Exception(
        Format("Tried to reference non-lvalue: ", ex)
      );
      return cast(Object) getSAPtr(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotSAPointer, "tree.rhs_partial.static_array_ptr");

// static array literal
class DataExpr : Expr {
  ubyte[] data;
  this(ubyte[] ub) { data = ub; }
  this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override IType valueType() { return new StaticArray(Single!(Char), data.length); }
  override void emitAsm(AsmFile af) {
    bool allNull = true;
    foreach (val; data) if (val) { allNull = false; break; }
    if (allNull) {
      af.pushStack(Format("$", 0), new StaticArray(Single!(Char), data.length)); // better optimizable
      return;
    }
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
