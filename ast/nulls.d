module ast.nulls;

import ast.base, ast.casting, ast.int_literal, ast.aliasing, ast.tuples, ast.fold;
import ast.arrays, ast.dg, ast.fun, ast.oop;
bool isNull(Expr ex) {
  auto ea = fastcast!(ExprAlias)~ ex;
  if (ea) ex = ea.base;
  auto rce = fastcast!(RCE)~ ex;
  if (!rce || Single!(Pointer, Single!(Void)) != rce.to) return false;
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
  auto e1vt = ex1.valueType(), e2vt = ex2.valueType();
  assert(e1vt.size == e2vt.size);
  if (e1vt.size == 4)
    return fastalloc!(Compare)(ex1, true, false, true, false, ex2);
  assert(e1vt.size == 8 || e1vt.size == 12);
  IType t2;
  if (e1vt.size == 8) t2 = mkTuple(voidp, voidp);
  if (e1vt.size == 12) t2 = mkTuple(voidp, voidp, voidp);
  if (!t2) fail;
  return ex2cond(tmpize_maybe(ex1, delegate Expr(Expr ex1) {
    return tmpize_maybe(ex2, delegate Expr(Expr ex2) {
      auto ex1s = getTupleEntries(reinterpret_cast(fastcast!(IType) (t2), ex1));
      auto ex2s = getTupleEntries(reinterpret_cast(fastcast!(IType) (t2), ex2));
      Cond cd;
      if (e1vt.size == 8) {
        cd = new BooleanOp!("||")(
          ex2cond(lookupOp("!=", ex1s[0], ex2s[0])),
          ex2cond(lookupOp("!=", ex1s[1], ex2s[1]))
        );
      }
      if (e1vt.size == 12) {
        cd = new BooleanOp!("||"[])(
          ex2cond(lookupOp("!=", ex1s[0], ex2s[0])), new BooleanOp!("||")(
          ex2cond(lookupOp("!=", ex1s[1], ex2s[1])),
          ex2cond(lookupOp("!=", ex1s[2], ex2s[2]))
        ));
      }
      if (!cd) fail;
      return cond2ex(cd);
    });
  }));
}

extern(C) Cond _testNonzero(Expr ex) {
  auto ex2 = ex, ex3 = ex; // test for int-like
  IType[] _tried;
  IType Bool = fastcast!(IType) (sysmod.lookup("bool"[]));
  if (gotImplicitCast(ex2,         Bool   , (IType it) { _tried ~= it; return test(it == Bool); }) || (ex2 = null, false)
    ||gotImplicitCast(ex3, Single!(SysInt), (IType it) { _tried ~= it; return test(Single!(SysInt) == it); }) || (ex3 = null, false)) {
    if (!ex2) ex2 = ex3;
    if (auto ce = fastcast!(CondExpr) (ex2)) return ce.cd;
    return exprwrap(ex2);
    // return fastalloc!(Compare)(ex2, true, false, true, false, mkInt(0)); // ex2 <> 0
  }
  auto n = fastcast!(Expr)~ sysmod.lookup("null");
  // if (!n) return null;
  if (!n) fail;
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
  // fail;
  return null;
}

Cond testNonzero(Expr ex) { return _testNonzero(ex); }

import ast.literals, ast.casting, ast.modules, ast.conditionals, ast.opers;
Object gotExprAsCond(ref string text, ParseCb cont, ParseCb rest) {
  Object obj;
  auto t2 = text;
  if (rest(t2, "tree.expr", &obj)) {
    if (fastcast!(Cond)(obj)) { text = t2; return obj; } // Okaaaay.
    auto ex = fastcast!(Expr) (obj);
    if (!ex) return null;
    if (t2.accept("."[])) return null; // wtf? definitely not a condition.
    if (auto res = testNonzero(ex)) { text = t2; return fastcast!(Object) (res); }
  }
  return null;
}
mixin DefaultParser!(gotExprAsCond, "cond.expr"[], "73"[]);
