module ast.nullcasts;

import ast.base, ast.casting, ast.int_literal, ast.aliasing, ast.tuples;
import ast.arrays, ast.dg, ast.fun, ast.oop;
bool isNull(Expr ex) {
  auto ea = cast(ExprAlias) ex;
  if (ea) ex = ea.base;
  auto rce = cast(RCE) ex;
  if (!rce) return false;
  ex = rce.from;
  auto ie = cast(IntExpr) ex;
  if (!ie) return false;
  return ie.num == 0;
}

static this() {
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && cast(FunctionPointer) expect) {
      return reinterpret_cast(expect, ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && cast(Delegate) expect) {
      return reinterpret_cast(expect, mkTupleExpr(ex, ex));
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && cast(Array) expect) {
      return reinterpret_cast(expect, mkTupleExpr(ex, ex));
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isNull(ex) && (cast(ClassRef) expect || cast(IntfRef) expect)) {
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
  auto sc = namespace().get!(Scope);
  // we'll be accessing members - generate temporaries.
  // Don't worry, they'll be cleaned up - conditions are guaranteed to
  // exist in an isolated scope.
  auto v1 = new Variable(ex1.valueType(), null, boffs(ex1.valueType()));
  v1.initval = ex1;
  sc.add(v1);
  auto v2 = new Variable(ex2.valueType(), null, boffs(ex2.valueType()));
  v2.initval = ex2;
  sc.add(v2);
  auto vd = new VarDecl;
  vd.vars ~= v1;
  vd.vars ~= v2;
  sc.addStatement(vd);
  auto ex1s = getTupleEntries(reinterpret_cast(cast(IType) t2, cast(LValue) v1));
  auto ex2s = getTupleEntries(reinterpret_cast(cast(IType) t2, cast(LValue) v2));
  return new BooleanOp!("||")(
    new ExprWrap(lookupOp("!=", ex1s[0], ex2s[0])),
    new ExprWrap(lookupOp("!=", ex1s[1], ex2s[1]))
  );
}

import ast.literals, ast.casting, ast.modules, ast.conditionals, ast.opers;
Object gotExprAsCond(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (rest(t2, "<tree.expr >tree.expr.cond", &ex)) {
    auto ex2 = ex; // test for int-like
    if (gotImplicitCast(ex2, (IType it) { return test(it == Single!(SysInt)); })) {
      text = t2;
      return new Compare(ex2, true, false, true, false, new IntExpr(0));
    }
    auto n = cast(Expr) sysmod.lookup("null");
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
      text = t2;
      return cast(Object) testNeq(cmp1, cmp2);
    }
    // logln("Failed overlaps: ", overlaps);
    return null;
  } else return null;
}
mixin DefaultParser!(gotExprAsCond, "cond.expr", "73");
