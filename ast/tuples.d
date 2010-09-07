module ast.tuples;

import ast.base, ast.structure, ast.casting;

/++
  1. A tuple behaves like a struct
  2. A tuple accepts index and slice notation.
  2.1. Excepting tuples with a size of one.
  3. A tuple autocasts to its first entry.
  4. A tuple is matched via '()' and ','.
++/

class Tuple : Type {
  /// 1.
  Structure wrapped;
  IType[] types() {
    IType[] res;
    wrapped.select((string, RelMember rm) { res ~= rm.type; });
    return res;
  }
  override {
    int size() { return wrapped.size; }
    string mangle() { return "tuple_"~wrapped.mangle(); }
    ubyte[] initval() { return wrapped.initval(); }
    string toString() { return Format("Tuple[", wrapped, "]"); }
    int opEquals(IType it) {
      if (!super.opEquals(it)) return false;
      while (true) {
        if (auto tp = cast(TypeProxy) it)
          it = tp.actualType();
        else break;
      }
      auto tup = cast(Tuple) it;
      assert(tup);
      auto sf1 = wrapped.stackframe, sf2 = tup.wrapped.stackframe;
      foreach (i, entry; sf1)
        if (entry != sf2[i]) return false;
      return true;
    }
  }
}

Object gotBraceExpr(ref string text, ParseCb cont, ParseCb rest) {
  Object obj; // exclusively for non-exprs.
  auto t2 = text;
  if (t2.accept("(") &&
      rest(t2, "tree.expr", &obj, (Object obj) { return !cast(Expr) obj; }) &&
      t2.accept(")")
    ) {
    text = t2;
    return obj;
  } else return null;
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces", "6");

Tuple mkTuple(IType[] types...) {
  auto tup = new Tuple;
  New(tup.wrapped, cast(string) null);
  foreach (type; types)
    new RelMember(null, type, tup.wrapped);
  return tup;
}

Expr mkTupleExpr(Expr[] exprs...) {
  auto tup = mkTuple(exprs /map/ (Expr ex) { return ex.valueType(); });
  return new RCE(tup, new StructLiteral(tup.wrapped, exprs));
}

/// 4.
import ast.math: AsmFloatBinopExpr;
Object gotTupleExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr[] exprs;
  Expr ex;
  auto t2 = text;
  if (t2.accept("(") &&
    t2.bjoin(
      !!rest(t2, "tree.expr", &ex),
      t2.accept(","),
      {
        exprs ~= ex;
      }
    ) && t2.accept(")")) {
    text = t2;
    return cast(Object) mkTupleExpr(exprs);
  } else return null;
}
mixin DefaultParser!(gotTupleExpr, "tree.expr.tuple", "60");