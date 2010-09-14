module ast.concat;

import
  ast.base, ast.parse, ast.arrays, ast.static_arrays, ast.int_literal,
  ast.vardecl, ast.scopes, ast.aggregate, ast.namespace, ast.index,
  ast.assign, ast.opers, ast.slice, tools.base: take;

class ConcatChain : Expr {
  Array type;
  Expr[] arrays;
  this(Expr[] exprs...) {
    if (!exprs.length) return;
    auto base = exprs.take();
    auto sa = cast(StaticArray) base.valueType();
    if (sa) {
      type = new Array(sa.elemType);
    } else {
      type = cast(Array) base.valueType();
      assert(!!type, Format(base, " is not array or static array! "));
    }
    addArray(base);
    foreach (expr; exprs)
      addArray(expr);
  }
  mixin DefaultDup!();
  mixin defaultIterate!(arrays);
  void addArray(Expr ex) {
    if (cast(StaticArray) ex.valueType()) arrays ~= staticToArray(ex);
    else arrays ~= ex;
  }
  override {
    IType valueType() { return type; }
    string toString() { return Format("~", arrays); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("valueType().size"));
      mkVar(af, type, true, (Variable var) {
        mixin(mustOffset("0"));
        auto sc = new Scope;
        namespace.set(sc);
        scope(exit) namespace.set(sc.sup);
        
        sc._body = Single!(NoOp);
        auto dg = sc.open(af);
        scope(exit) dg()();
        
        auto sa = new StaticArray(valueType(), arrays.length);
        auto
          offset = new Variable(Single!(SysInt), null, boffs(Single!(SysInt), af.currentStackDepth)),
          total  = new Variable(Single!(SysInt), null, boffs(Single!(SysInt), af.currentStackDepth + nativeIntSize)),
          cache  = new Variable(sa,              null, boffs(sa             , af.currentStackDepth + nativeIntSize * 2));
        cache.dontInit = true;
        {
          auto vd = new VarDecl;
          vd.vars ~= offset;
          vd.vars ~= total;
          vd.vars ~= cache;
          vd.emitAsm(af);
        }
        foreach (i, array; arrays) {
          (new Assignment(getIndex(cache, new IntExpr(i)), array)).emitAsm(af);
          iparse!(Statement, "gather_array_length", "tree.semicol_stmt.assign")
          (
            "total = total + cache[i].length",
            "total", total, "i", new IntExpr(i), "cache", cache
          ).emitAsm(af);
        }
        iparse!(Statement, "alloc_array", "tree.semicol_stmt.assign")
        (
          "var = new(total) T",
          "var", var, "T", type,
          "total", total
        ).emitAsm(af);
        foreach (i, array; arrays) {
          auto c = getIndex(cache, new IntExpr(i)), len = getArrayLength(c);
          /// var[offset .. offset + cache[i].length] = cache[i];
          (getSliceAssign(mkArraySlice(var, offset, lookupOp("+", offset, len)), c)).emitAsm(af);
          /// offset = offset + cache[i].length;
          (new Assignment(offset, lookupOp("+", offset, len))).emitAsm(af);
        }
      });
    }
  }
}

static this() {
  bool isArray(IType it) { return !!cast(Array) it; }
  bool isExtArray(IType it) { return !!cast(ExtArray) it; }
  defineOp("~", delegate Expr(Expr ex1, Expr ex2) {
    auto cc = cast(ConcatChain) ex1;
    if (!cc || !gotImplicitCast(ex2, &isArray))
      return null;
    return new ConcatChain(cc.arrays ~ ex2);
  });
  defineOp("~", delegate Expr(Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex1, &isArray) || !gotImplicitCast(ex2, &isArray))
      return null;
    return new ConcatChain(ex1, ex2);
  });
  defineOp("~", delegate Expr(Expr ex1, Expr ex2) {
    if (!isExtArray(ex1.valueType()) || !gotImplicitCast(ex2, &isArray))
      return null;
    if (!cast(LValue) ex1) {
      logln("Cannot concatenate ext+array: ext is not lvalue; cannot invalidate: ", ex1, ex2);
      asm { int 3; }
    }
    auto ea = cast(ExtArray) ex1.valueType();
    if (ea.freeOnResize) {
      return iparse!(Expr, "concat_into_ext_fOR", "tree.expr")
                    (`sys.append3!T(&l, r)`,
                    namespace(),
                    "T", ea.elemType, "l", ex1, "r", ex2);
    } else {
      return iparse!(Expr, "concat_into_ext", "tree.expr")
                    (`sys.append2!T(&l, r)`,
                    namespace(),
                    "T", ea.elemType, "l", ex1, "r", ex2);
    }
  });
  defineOp("~", delegate Expr(Expr ex1, Expr ex2) {
    logln("op: concat");
    logln("ex1: ", ex1.valueType());
    logln("ex2: ", ex2.valueType());
    asm { int 3;}
    return null;
  });
}

import ast.casting;
Object gotConcatChain(ref string text, ParseCb cont, ParseCb rest) {
  Expr op, op2;
  auto t2 = text;
  IType elemtype;
  if (!cont(t2, &op)) return null;
  auto first = op;
  retry:
  if (t2.accept("~") && cont(t2, &op2)) {
    op = lookupOp("~", op, op2);
    if (!op) return null;
    goto retry;
  }
  if (op is first) return null;
  text = t2;
  return cast(Object) op;
}
mixin DefaultParser!(gotConcatChain, "tree.expr.arith.concat", "305");
