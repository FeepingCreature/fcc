module ast.concat;

import
  ast.base, ast.parse, ast.arrays, ast.static_arrays, ast.int_literal,
  ast.vardecl, ast.scopes, ast.aggregate, ast.namespace, ast.index,
  ast.assign, ast.math, ast.slice;

class ConcatChain : Expr {
  Array type;
  Expr[] arrays;
  this(Expr base) {
    auto sa = cast(StaticArray) base.valueType();
    if (sa) {
      type = new Array(sa.elemType);
    } else {
      type = cast(Array) base.valueType();
      assert(!!type, Format(base, " is not array or static array! "));
    }
    addArray(base);
  }
  private this() { }
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
          (getSliceAssign(mkArraySlice(var, offset, new AddExpr(offset, len)), c)).emitAsm(af);
          /// offset = offset + cache[i].length;
          (new Assignment(offset, new AddExpr(offset, len))).emitAsm(af);
        }
      });
    }
  }
}

import ast.casting;
Object gotConcatChain(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  IType elemtype;
  if (!cont(t2, &op) || !gotImplicitCast(op, (IType it) { return !!cast(Array) it || !!cast(StaticArray) it; })) return null;
  if (auto ar = cast(Array) op.valueType()) {
    elemtype = ar.elemType;
  } else if (auto sa = cast(StaticArray) op.valueType()) {
    elemtype = sa.elemType;
  } else return null;
  auto cc = new ConcatChain(op);
  string t3;
  if (t2.many(
    (t3 = t2, true) &&
    t2.accept("~") && cont(t2, &op) && gotImplicitCast(op, (IType it) {
      if (auto ar = cast(Array) it)
        return !!(elemtype == ar.elemType);
      else return false;
    }),
    { cc.addArray(op); }
  )) {
    if (cc.arrays.length == 1) return null; // many matches on none
    text = t2;
    return cc;
  } else {
    if (t3.accept("~"))
      throw new Exception("Failed to parse concatenation at '"~t2.next_text()~"'");
    return null;
  }
}
mixin DefaultParser!(gotConcatChain, "tree.expr.arith.concat", "305");
