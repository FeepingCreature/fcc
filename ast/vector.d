module ast.vector;

import ast.base, ast.tuples, ast.tuple_access, ast.types, ast.fold;
import ast.structure, ast.namespace;

class Vector : Type, RelNamespace {
  IType base;
  Tuple asTup;
  int len;
  this(IType it, int i) {
    this.base = it;
    this.len = i;
    IType[] mew;
    for (int k = 0; k < i; ++k)
      mew ~= it;
    asTup = mkTuple(mew);
  }
  override {
    int size() { return asTup.size; }
    string mangle() { return Format("vec_", len, "_", base.mangle()); }
    ubyte[] initval() { return asTup.initval(); }
    int opEquals(IType it) {
      if (!super.opEquals(it)) return false;
      while (true) {
        if (auto tp = cast(TypeProxy) it)
          it = tp.actualType();
        else break;
      }
      auto vec = cast(Vector) it;
      assert(vec);
      return vec.base == base && vec.len == len;
    }
    Object lookupRel(string str, Expr base) {
      if (!base) return null;
      if (len > 4) return null;
      bool isValidChar(char c) {
        if (len >= 1 && c == 'x') return true;
        if (len >= 2 && c == 'y') return true;
        if (len >= 3 && c == 'z') return true;
        if (len == 4 && c == 'w') return true;
        return false;
      }
      foreach (ch; str) if (!isValidChar(ch)) return null;
      auto parts = getTupleEntries(reinterpret_cast(asTup, base));
      Expr[] exprs;
      foreach (ch; str) {
             if (ch == 'x') exprs ~= parts[0];
        else if (ch == 'y') exprs ~= parts[1];
        else if (ch == 'z') exprs ~= parts[2];
        else if (ch == 'w') exprs ~= parts[3];
        else assert(false);
      }
      if (exprs.length == 1) return cast(Object) exprs[0];
      return cast(Object) reinterpret_cast(new Vector(this.base, exprs.length), mkTupleExpr(exprs));
    }
  }
}

Object gotVecConstructor(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  while (true) {
    if (auto tp = cast(TypeProxy) ty) {
      ty = tp.actualType;
      continue;
    }
    break;
  }
  auto vec = cast(Vector) ty;
  if (!vec)
    return null;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex)) return null;
  auto ex2 = ex;
  if (gotImplicitCast(ex2, (IType it) { return test(it == vec.base); })) {
    Expr[] exs;
    for (int i = 0; i < vec.len; ++i)
      exs ~= ex2.dup;
    text = t2;
    return cast(Object)
      reinterpret_cast(vec, new StructLiteral(vec.asTup.wrapped, exs));
  }
  auto tup = cast(Tuple) ex.valueType();
  if (tup) {
    if (tup.types.length != vec.len)
      throw new Exception("Insufficient elements in vec initializer! ");
    Expr[] exs;
    foreach (entry; getTupleEntries(ex)) {
      if (!gotImplicitCast(entry, (IType it) { return test(it == vec.base); }))
        throw new Exception(Format("Invalid type in vec initializer: ", entry));
      exs ~= entry;
    }
    text = t2;
    return cast(Object)
      reinterpret_cast(vec, new StructLiteral(vec.asTup.wrapped, exs));
  }
  assert(false);
}
mixin DefaultParser!(gotVecConstructor, "tree.expr.veccon", "8");

import ast.casting, ast.static_arrays;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = cast(Vector) ex.valueType()) {
      return reinterpret_cast(new StaticArray(vec.base, vec.len), ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = cast(Vector) ex.valueType()) {
      IType[] types;
      for (int i = 0; i < vec.len; ++i)
        types ~= vec.base;
      return reinterpret_cast(mkTuple(types), ex);
    }
    return null;
  };
}

import ast.parse, ast.int_literal;
Object gotVecType(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType it;
  Expr len;
  if (!t2.accept("vec(")) return null;
  if (!rest(t2, "type", &it) ||
      !t2.accept(",") ||
      !rest(t2, "tree.expr", &len) ||
      !t2.accept(")"))
    t2.failparse("Fail to parse vector");
  auto ie = cast(IntExpr) fold(len);
  if (!ie)
    text.failparse("Size parameter to vec not foldable or int");
  text = t2;
  return new Vector(it, ie.num);
}
mixin DefaultParser!(gotVecType, "type.vector", "34");

import ast.opers;
static this() {
  Expr handleVecOp(string op, Expr lhs, Expr rhs) {
    auto v1 = lhs.valueType(), v2 = rhs.valueType();
    bool pretransform(ref Expr ex, ref IType it) {
      if (auto tp = cast(TypeProxy) it) {
        it = tp.actualType;
        return true;
      }
      if (auto tup = cast(Tuple) it) {
        if (tup.types.length == 1) {
          ex = getTupleEntries(ex)[0];
          it = tup.types[0];
          return true;
        }
      }
      return false;
    }
    while (true) {
      if (pretransform(lhs, v1)) continue;
      if (pretransform(rhs, v2)) continue;
      break;
    }
    auto v1v = cast(Vector) v1, v2v = cast(Vector) v2;
    if (!v1v && !v2v) return null;
    
    assert(!v1v || !v2v || v1v == v2v);
    Vector vt;
    if (v1v) vt = v1v;
    else vt = v2v;
    Expr[] list;
    for (int i = 0; i < vt.asTup.types.length; ++i) {
      auto exl = lhs, exr = rhs;
      if (v1v) exl = getTupleEntries(reinterpret_cast(v1v.asTup, exl))[i];
      if (v2v) exr = getTupleEntries(reinterpret_cast(v2v.asTup, exr))[i];
      list ~= lookupOp(op, exl, exr);
    }
    return reinterpret_cast(vt, new StructLiteral(vt.asTup.wrapped, list));
  }
  defineOp("-", "-" /apply/ &handleVecOp);
  defineOp("+", "+" /apply/ &handleVecOp);
  defineOp("*", "*" /apply/ &handleVecOp);
  defineOp("/", "/" /apply/ &handleVecOp);
}
