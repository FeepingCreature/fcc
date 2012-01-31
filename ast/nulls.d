module ast.nulls;

import ast.base, ast.casting, ast.int_literal, ast.aliasing, ast.tuples;
import ast.arrays, ast.dg, ast.fun, ast.oop;
bool isNull(Expr ex) {
  auto ea = fastcast!(ExprAlias)~ ex;
  if (ea) ex = ea.base;
  auto rce = fastcast!(RCE)~ ex;
  if (!rce) return false;
  ex = rce.from;
  auto ie = fastcast!(IntExpr)~ ex;
  if (!ie) return false;
  return ie.num == 0;
}

static this() {
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && fastcast!(FunctionPointer) (resolveType(expect))) {
      return reinterpret_cast(expect, ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && fastcast!(Delegate) (resolveType(expect))) {
      return reinterpret_cast(expect, mkTupleExpr(ex, ex));
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && fastcast!(Array) (resolveType(expect))) {
      return reinterpret_cast(expect, mkTupleExpr(ex, ex));
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && fastcast!(ExtArray) (resolveType(expect))) {
      return reinterpret_cast(expect, mkTupleExpr(ex, ex, ex));
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && (
      fastcast!(ClassRef)(resolveType(expect))
    ||fastcast!(IntfRef)(resolveType(expect)))) {
      return reinterpret_cast(expect, ex);
    }
    return null;
  };
}

import ast.pointer, ast.tuples, ast.tuple_access, ast.namespace, ast.scopes, ast.variable, ast.vardecl;
Cond testNeq(Expr ex1, Expr ex2) {
  assert(ex1.valueType().size == ex2.valueType().size);
  if (ex1.valueType().size == 4)
    return new Compare(ex1, true, false, true, false, ex2);
  assert(ex1.valueType().size == 8);
  auto t2 = mkTuple(voidp, voidp);
  return new ExprWrap(tmpize_maybe(ex1, delegate Expr(Expr ex1) {
    return tmpize_maybe(ex2, delegate Expr(Expr ex2) {
      auto ex1s = getTupleEntries(reinterpret_cast(fastcast!(IType) (t2), ex1));
      auto ex2s = getTupleEntries(reinterpret_cast(fastcast!(IType) (t2), ex2));
      Cond cd = new BooleanOp!("||")(
        new ExprWrap(lookupOp("!=", ex1s[0], ex2s[0])),
        new ExprWrap(lookupOp("!=", ex1s[1], ex2s[1]))
      );
      return new CondExpr(cd);
    });
  }));
  /*auto v1 = lvize(ex1, &init1);
  auto v2 = lvize(ex2, &init2);
  auto ex1s = getTupleEntries(reinterpret_cast(fastcast!(IType)~ t2, fastcast!(LValue)~ v1));
  auto ex2s = getTupleEntries(reinterpret_cast(fastcast!(IType)~ t2, fastcast!(LValue)~ v2));
  Cond res = new BooleanOp!("||")(
    new ExprWrap(lookupOp("!=", ex1s[0], ex2s[0])),
    new ExprWrap(lookupOp("!=", ex1s[1], ex2s[1]))
  );
  if (init1) res = new StatementAndCond(init1, res);
  if (init2) res = new StatementAndCond(init2, res);
  return res;*/
}

Cond testNonzero(Expr ex) {
  auto ex2 = ex, ex3 = ex; // test for int-like
  IType[] _tried;
  IType Bool = fastcast!(IType) (sysmod.lookup("bool"));
  if (gotImplicitCast(ex2,         Bool   , (IType it) { _tried ~= it; return test(it == Bool); }) || (ex2 = null, false)
    || gotImplicitCast(ex3, Single!(SysInt), (IType it) { _tried ~= it; return test(Single!(SysInt) == it); }) || (ex3 = null, false)) {
    if (!ex2) ex2 = ex3;
    return new Compare(ex2, true, false, true, false, mkInt(0)); // ex2 <> 0
  }
  auto n = fastcast!(Expr)~ sysmod.lookup("null");
  if (!n) return null;
  auto ev = ex.valueType();
  Expr cmp1, cmp2;
  Stuple!(IType, IType)[] overlaps;
  void test(Expr e1, Expr e2) {
    auto i1 = e1.valueType(), i2 = e2.valueType();
    Expr e1t;
    if (gotImplicitCast(e1, i2, (IType it) {
      auto e2t = e2;
      auto res = gotImplicitCast(e2t, it, (IType it2) {
        overlaps ~= stuple(it,  it2);
        return .test(it == it2);
      });
      if (res) cmp2 = e2t;
      return res;
    })) { cmp1 = e1; }
  }
  test(ex, n);
  if (!cmp1) test(n, ex);
  if (cmp1 && cmp2) {
    return testNeq(cmp1, cmp2);
  }
  // logln("Failed overlaps: ", overlaps);
  return null;
}

import ast.literals, ast.casting, ast.modules, ast.conditionals, ast.opers;
Object gotExprAsCond(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex; Cond cd;
  auto t2 = text;
  if (rest(t2, "<tree.expr >tree.expr.cond", &cd) || rest(t2, "<tree.expr >tree.expr.cond", &ex)) {
    if (cd) { text = t2; return fastcast!(Object) (cd); } // Okaaaay.
    if (!ex) return null;
    if (auto res = testNonzero(ex)) { text = t2; return fastcast!(Object) (res); }
    if (t2.accept(".")) return null; // wtf? definitely not a condition.
  } else return null;
}
mixin DefaultParser!(gotExprAsCond, "cond.expr", "99");
