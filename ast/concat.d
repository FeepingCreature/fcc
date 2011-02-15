module ast.concat;

import
  ast.base, ast.parse, ast.arrays, ast.static_arrays, ast.int_literal,
  ast.vardecl, ast.scopes, ast.aggregate, ast.namespace, ast.index,
  ast.assign, ast.opers, ast.slice, ast.fold, tools.base: take;

class ConcatChain : Expr {
  Array type;
  Expr[] arrays;
  this(Expr[] exprs...) {
    if (!exprs.length) return;
    auto base = exprs.take();
    auto sa = fastcast!(StaticArray)~ base.valueType();
    if (sa) {
      type = new Array(sa.elemType);
    } else {
      type = fastcast!(Array)~ base.valueType();
      assert(!!type, Format(base, " is not array or static array! "));
    }
    addArray(base);
    foreach (expr; exprs)
      addArray(expr);
  }
  mixin DefaultDup!();
  mixin defaultIterate!(arrays);
  void addArray(Expr ex) {
    if (fastcast!(StaticArray)~ ex.valueType()) arrays ~= staticToArray(ex);
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
          if (array.valueType() == type.elemType) {
            iparse!(Statement, "inc_array_length", "tree.stmt")
                   (`total ++; `, "total", total).emitAsm(af);
          } else {
            // cache[i] = array
            auto cachepos = getIndex(cache, mkInt(i));
            (new Assignment(cachepos, array)).emitAsm(af);
            // total = total + cache[i].length
            (new Assignment(total,
              lookupOp("+", total, getArrayLength(cachepos))
            )).emitAsm(af);
          }
        }
        iparse!(Statement, "alloc_array", "tree.semicol_stmt.assign")
        (
          "var = new T[total]",
          "var", var, "T", type.elemType,
          "total", total
        ).emitAsm(af);
        foreach (i, array; arrays) {
          auto c = getIndex(cache, mkInt(i));
          if (array.valueType() == type.elemType) {
            /// var[offset] = cache[i];
            (new Assignment(getIndex(var, offset), array)).emitAsm(af);
            /// offset = offset + 1
            (new Assignment(offset, lookupOp("+", offset, mkInt(1)))).emitAsm(af);
          } else {
            auto len = getArrayLength(c);
            /// var[offset .. offset + cache[i].length] = cache[i];
            optst(getSliceAssign(mkArraySlice(var, offset, lookupOp("+", offset, len)), c.dup)).emitAsm(af);
            /// offset = offset + cache[i].length;
            optst(new Assignment(offset, lookupOp("+", offset, len))).emitAsm(af);
          }
        }
      });
    }
  }
}

static this() {
  bool isArray(IType it) { return fastcast!(Array) (it) || fastcast!(StaticArray) (it); }
  bool isExtArray(IType it) { return !!fastcast!(ExtArray) (it); }
  bool isEqual(IType i1, IType i2) {
    return test(resolveType(i1) == resolveType(i2));
  }
  defineOp("~", delegate Expr(Expr ex1, Expr ex2) {
    auto cc = cast(ConcatChain) ex1, ex22 = ex2; // lol
    if (!cc || !gotImplicitCast(ex2, &isArray) && !gotImplicitCast(ex22, cc.type.elemType /apply/ &isEqual))
      return null;
    if (!ex2) ex2 = ex22;
    return new ConcatChain(cc.arrays ~ ex2);
  });
  defineOp("~", delegate Expr(Expr ex1, Expr ex2) {
    auto ex22 = ex2;
    if (
      !gotImplicitCast(ex1, &isArray)
      ||
        !gotImplicitCast(ex2, &isArray)
        &&
        !gotImplicitCast(ex22, (fastcast!(Array)~ ex1.valueType()).elemType /apply/ &isEqual)
      )
      return null;
    if (!ex2) ex2 = ex22;
    return new ConcatChain(ex1, ex2);
  });
  defineOp("~", delegate Expr(Expr ex1, Expr ex2) {
    auto e1vt = resolveType(ex1.valueType());
    if (
      !isExtArray(e1vt) ||
      !gotImplicitCast(ex2, (IType it) {
        return test(new Array((fastcast!(ExtArray)~ e1vt).elemType) == it);
      }))
      return null;
    if (!fastcast!(LValue) (ex1)) {
      logln("Cannot concatenate ext+array: ext is not lvalue; cannot invalidate: ", ex1, ex2);
      asm { int 3; }
    }
    auto ea = fastcast!(ExtArray)~ e1vt;
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
    auto e1vt = resolveType(ex1.valueType());
    if (!isExtArray(e1vt)) return null;
    auto et = resolveType((fastcast!(ExtArray)~ e1vt).elemType);
    if (!gotImplicitCast(ex2, (IType it) { return !!(it == et); }))
      return null;
    if (!fastcast!(LValue) (ex1)) {
      logln("Cannot concatenate ext+elem: ext is not lvalue; cannot invalidate: ", ex1, ex2);
      asm { int 3; }
    }
    auto ea = fastcast!(ExtArray)~ e1vt;
    if (ea.freeOnResize) {
      return iparse!(Expr, "concat_into_ext_fOR_elem", "tree.expr")
                    (`sys.append3e!T(&l, r)`, namespace(),
                    "T", ea.elemType, "l", ex1, "r", ex2);
    } else {
      return iparse!(Expr, "concat_into_ext_elem", "tree.expr")
                    (`sys.append2e!T(&l, r)`, namespace(),
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
  auto t3 = t2;
  if (t3.accept("~=") && cont(t3, &op2)) {
    op = lookupOp("~=", op, op2);
    if (!op) return null;
    t2 = t3;
    goto retry;
  }
  if (t2.accept("~") && cont(t2, &op2)) {
    op = lookupOp("~", op, op2);
    if (!op) return null;
    goto retry;
  }
  if (op is first) return null;
  text = t2;
  return fastcast!(Object)~ op;
}
mixin DefaultParser!(gotConcatChain, "tree.expr.arith.concat", "305");
