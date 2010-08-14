module ast.concat;

import
  ast.base, ast.parse, ast.arrays, ast.static_arrays,
  ast.vardecl, ast.scopes, ast.aggregate, ast.namespace;

class ConcatChain : Expr {
  Array type;
  Expr[] arrays;
  mixin defaultIterate!(arrays);
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
  void addArray(Expr ex) {
    if (cast(StaticArray) ex.valueType()) arrays ~= staticToArray(ex);
    else arrays ~= ex;
  }
  override {
    IType valueType() { return type; }
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
        
        auto
          offset = new Variable(Single!(SysInt), null, boffs(Single!(SysInt), af.currentStackDepth)),
          total = new Variable(Single!(SysInt), null, boffs(Single!(SysInt), af.currentStackDepth + nativeIntSize));
        {
          auto vd = new VarDecl;
          vd.vars ~= offset;
          vd.vars ~= total;
          vd.emitAsm(af);
        }
        foreach (array; arrays) {
          auto len = getArrayLength(array);
          iparse!(Statement, "gather_array_length", "tree.semicol_stmt.assign")
          (
            "total = total + array.length",
            "total", total, "array", array
          ).emitAsm(af);
        }
        iparse!(Statement, "alloc_array", "tree.semicol_stmt.assign")
        (
          "var = new(total) T",
          "var", var, "T", type,
          "total", total
        ).emitAsm(af);
        foreach (array; arrays) {
          auto len = getArrayLength(array);
          iparse!(Scope, "set_result_array", "tree.scope")
          (
            "{
                printf(\"var[%i .. %i + %i] = %i %.*s; \n\", offset, offset, len, array);
                var[offset .. offset + len] = array;
                printf(\"var: %i %i %p @%p\n\", var, &var);
                offset = offset + len;
              }",
            "var", var, "offset", offset,
            "len", len, "array", array
          ).emitAsm(af);
        }
      });
    }
  }
}

Object gotConcatChain(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  IType elemtype;
  if (!cont(t2, &op)) return null;
  if (auto ar = cast(Array) op.valueType()) {
    elemtype = ar.elemType;
  } else if (auto sa = cast(StaticArray) op.valueType()) {
    elemtype = sa.elemType;
  } else return null;
  auto cc = new ConcatChain(op);
  string t3;
  if (t2.many(
    (t3 = t2, true) &&
    t2.accept("~") && cont(t2, &op,
      (Expr ex) {
        if (auto ar = cast(Array) ex.valueType()) {
          return !!(elemtype == ar.elemType);
        } else return false;
      }
    ),
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
