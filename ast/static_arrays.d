module ast.static_arrays;

import ast.base, ast.types;

class StaticArray : Type {
  IType elemType;
  int length;
  this() { }
  this(IType et, int len) { elemType = et; length = len; }
  override string toString() { return Format(elemType, "[", length, "]"); }
  override int size() {
    return length * elemType.size();
  }
  override string mangle() {
    return Format("Static_", length, "_of_", elemType.mangle());
  }
  override int opEquals(IType ty) {
    ty = resolveType(ty);
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
      auto len = fold(len_ex);
      if (auto ie = cast(IntExpr) len) {
        text = t2;
        return new StaticArray(cur, ie.num);
      }
      return null;
      // throw new Exception(Format("Not a constant: ", len));
    } else return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (!cast(StaticArray) ex.valueType() || !cast(CValue) ex)
      return null;
    return getSAPtr(ex);
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
  assert(cast(CValue) sa);
  return new ReinterpretCast!(Expr) (new Pointer(vt.elemType), new RefExpr(cast(CValue) sa));
}

import ast.parse, ast.namespace, ast.int_literal, ast.pointer, ast.casting;
Object gotSAPointer(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = cast(StaticArray) ex.valueType()) {
      if (!text.accept(".ptr")) return null;
      auto cv = cast(CValue) ex;
      if (!cv) throw new Exception(
        Format("Tried to reference non-cvalue for .ptr: ", ex)
      );
      return cast(Object) getSAPtr(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotSAPointer, "tree.rhs_partial.static_array_ptr");

// static array literal 1
class DataExpr : Expr {
  ubyte[] data;
  this(ubyte[] ub) { data = ub; }
  this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override IType valueType() { return new StaticArray(Single!(Char), data.length); }
  override string toString() { return Format(data); }
  override void emitAsm(AsmFile af) {
    bool allNull = true;
    foreach (val; data) if (val) { allNull = false; break; }
    if (allNull) {
      af.flush();
      auto backup = af.optimize;
      // don't even try to opt this
      af.optimize = false;
      af.pushStack(Format("$", 0), new StaticArray(Single!(Char), data.length)); // better optimizable
      af.flush();
      af.optimize = backup;
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

class SALiteralExpr : Expr {
  Expr[] exs;
  mixin DefaultDup!();
  mixin defaultIterate!(exs);
  IType type;
  override {
    IType valueType() { return new StaticArray(type, exs.length); }
    void emitAsm(AsmFile af) {
      // stack emit order: reverse!
      // TODO: Alignment.
      foreach_reverse (ex; exs)
        ex.emitAsm(af);
    }
    string toString() { return Format("SA literal ", exs); }
  }
}

Object gotSALiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("[")) return null;
  Expr ex;
  auto res = new SALiteralExpr;
  if (!t2.bjoin(
    !!rest(t2, "tree.expr", &ex),
    t2.accept(","),
    {
      IType[] types;
      if (!res.type) res.type = ex.valueType();
      else if (!gotImplicitCast(ex, (IType it) { types ~= it; return test(it == res.type); }))
        t2.failparse("Invalid SA literal member; none of ", types, " match ", res.type);
      res.exs ~= ex;
    }
  )) t2.failparse("Failed to parse array literal");
  if (!t2.accept("]"))
    t2.failparse("Expected closing ']'");
  text = t2;
  return res;
}
mixin DefaultParser!(gotSALiteral, "tree.expr.literal.array", "52");
