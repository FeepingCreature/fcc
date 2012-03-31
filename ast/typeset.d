module ast.typeset;

import ast.base, ast.types, ast.tuples, ast.casting, ast.vardecl, ast.tuple_access, ast.fold, ast.namespace;

class Typeset : Type, RelNamespace {
  Tuple tup;
  mixin MyThis!("tup");
  override {
    int size() { return tup.size; }
    ubyte[] initval() { return tup.initval; }
    int opEquals(IType it) {
      auto tys = fastcast!(Typeset) (resolveType(it));
      if (!tys) return false;
      return tup == tys.tup;
    }
    string mangle() { return "typeset_over_"~tup.mangle(); }
    bool isTempNamespace() { return false; }
    Object lookupRel(string name, Expr base, bool isDirectLookup = true) {
      auto tup_ex = reinterpret_cast(tup, base);
      foreach (i, ty; tup.types) {
        if (auto srn = fastcast!(SemiRelNamespace) (ty)) ty = fastcast!(IType) (srn.resolve());
        auto rn = fastcast!(RelNamespace) (ty);
        if (rn) {
          if (auto res = rn.lookupRel(name, mkTupleIndexAccess(tup_ex, i), isDirectLookup))
            return res; // TODO: overloading maybe
        }
      }
      return null;
    }
  }
}

static this() {
  // first implicit conversion
  // convert any matching expr to a typeset (if requested)
  implicits ~= delegate void(Expr ex, IType dest, void delegate(Expr) consider) {
    auto tys = fastcast!(Typeset) (dest);
    if (!tys) return;
    foreach (type; tys.tup.types()) {
      auto ex2 = ex;
      if (!gotImplicitCast(ex2, type, (IType it) { return !!(type == it); }))
        return;
    }
    consider(tmpize_maybe(ex, (Expr ex) {
      Expr[] exprs;
      foreach (type; tys.tup.types()) {
        auto ex2 = ex;
        if (!gotImplicitCast(ex2, type, (IType it) { return !!(type == it); }))
          fail; // wat
        exprs ~= ex2;
      }
      return reinterpret_cast(tys, mkTupleExpr(exprs));
    }));
  };
  implicits ~= delegate void(Expr ex, void delegate(Expr) consider) {
    auto tys = fastcast!(Typeset) (ex.valueType());
    if (!tys) return;
    auto ex_as_tup = foldex(reinterpret_cast(tys.tup, ex));
    foreach (i, type; tys.tup.types()) {
      consider(mkTupleIndexAccess(ex_as_tup, i));
    }
  };
}

Object gotTypeset(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  Tuple tup;
  // if (!rest(t2, "type.tuple", &tup))
  //   t2.failparse("Tuple expected");
  IType[] typelist;
  if (!t2.accept("<")) return null;
  while (true) {
    if (t2.accept(">")) break;
    if (typelist.length) if (!t2.accept(",")) return null;
    IType ty;
    if (!rest(t2, "type", &ty)) {
      if (typelist.length) // definitely a typeset wanted
        t2.failparse("type expected");
      else
        return null;
    }
    typelist ~= ty;
  }
  tup = mkTuple(typelist);
  text = t2;
  return new Typeset(tup);
}
mixin DefaultParser!(gotTypeset, "type.set", "61");
