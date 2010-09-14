module ast.vector;

import ast.base, ast.tuples, ast.tuple_access, ast.types, ast.fold;

class Vector : Type {
  IType base;
  int len;
  this(IType it, int i) { this.base = it; this.len = i; }
  override {
    int size() { return base.size * len; }
    string mangle() { return Format("vec_", len, "_", base.mangle()); }
    ubyte[] initval() { ubyte[] res; for (int i = 0; i < len; ++i) res ~= base.initval(); return res; }
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
  }
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
    throw new Exception("Fail to parse vector at '"~t2.next_text());
  auto ie = cast(IntExpr) fold(len);
  if (!ie)
    throw new Exception("Size parameter to vec not foldable or int: '"~text.next_text()~"'! ");
  text = t2;
  return new Vector(it, ie.num);
}
mixin DefaultParser!(gotVecType, "type.vector", "34");
