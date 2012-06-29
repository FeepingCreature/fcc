module ast.concat;

import
  ast.base, ast.parse, ast.arrays, ast.static_arrays, ast.int_literal,
  ast.vardecl, ast.scopes, ast.aggregate, ast.namespace, ast.index,
  ast.assign, ast.opers, ast.slice, ast.fold, ast.literal_string, ast.literals, tools.base: take;

class ConcatChain : Expr {
  Array type;
  Expr[] arrays;
  this(Expr[] exprs...) {
    if (!exprs.length) return;
    auto base = exprs.take();
    auto sa = fastcast!(StaticArray)~ base.valueType();
    if (sa) {
      type = fastalloc!(Array)(sa.elemType);
    } else {
      type = fastcast!(Array)~ base.valueType();
      assert(!!type, Format(base, " is not array or static array! "[]));
    }
    addArray(base);
    foreach (expr; exprs)
      addArray(expr);
  }
  mixin DefaultDup!();
  mixin defaultIterate!(arrays);
  void addArray(Expr ex) {
    Expr nuArray;
    if (fastcast!(StaticArray)~ ex.valueType()) nuArray = staticToArray(ex);
    else nuArray = ex;
    if (arrays.length) {
      auto se1 = fastcast!(StringExpr) (foldex(arrays[$-1]));
      auto se2 = fastcast!(StringExpr) (foldex(nuArray));
      if (se1 && se2) {
        arrays[$-1] = mkString(se1.str~se2.str);
        return;
      }
    }
    arrays ~= nuArray;
  }
  override {
    IType valueType() { return type; }
    string toString() { return Format("~"[], arrays); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("valueType().size"[]));
      mkVar(af, type, true, (Variable var) {
        mixin(mustOffset("0"[]));
        auto sc = new Scope;
        namespace.set(sc);
        scope(exit) namespace.set(sc.sup);
        sc.requiredDepth = af.currentStackDepth;
        
        sc._body = Single!(NoOp);
        auto dg = sc.open(af);
        scope(exit) dg()(false);
        
        string lit;
        bool isLiteral(Expr ex) {
          if (auto se = fastcast!(StringExpr) (foldex(ex))) {
            lit = se.str;
            return true;
          }
          return false;
        }
        
        int cacheNeeded;
        foreach (array; arrays)
          if (array.valueType() != type.elemType && !isLiteral(array)) cacheNeeded ++;
          
        auto sa = fastalloc!(StaticArray)(valueType(), cacheNeeded);
        auto
          offset = fastalloc!(Variable)(Single!(SysInt), cast(string) null, boffs(Single!(SysInt), af.currentStackDepth)),
          total  = fastalloc!(Variable)(Single!(SysInt), cast(string) null, boffs(Single!(SysInt), af.currentStackDepth + nativeIntSize)),
          cache  = fastalloc!(Variable)(sa,              cast(string) null, boffs(sa             , af.currentStackDepth + nativeIntSize * 2));
        
        cache.dontInit = true;
        int literals_len;
        foreach (array; arrays)
          if (array.valueType() != type.elemType && isLiteral(array))
            literals_len += lit.length;
        
        total.initval = mkInt(literals_len);
        total.initInit;
        offset.initInit;
        (fastalloc!(VarDecl)(offset)).emitAsm(af);
        (fastalloc!(VarDecl)(total)).emitAsm(af);
        (fastalloc!(VarDecl)(cache)).emitAsm(af);
        int cacheId = 0;
        foreach (array; arrays) {
          if (array.valueType() == type.elemType) {
            iparse!(Statement, "inc_array_length"[], "tree.stmt"[])
                   (`total ++; `, "total"[], total).emitAsm(af);
          } else {
            if (isLiteral(array)) continue;
            // cache[i] = array
            auto cachepos = getIndex(cache, mkInt(cacheId++));
            emitAssign(af, cachepos, array);
            // total = total + cache[i].length
            emitAssign(af, total, lookupOp("+"[], total, getArrayLength(cachepos)));
          }
        }
        iparse!(Statement, "alloc_array"[], "tree.semicol_stmt.assign"[])
        (
          "var = new T[] total"[],
          "var"[], var, "T"[], type.elemType,
          "total"[], total
        ).emitAsm(af);
        cacheId = 0;
        foreach (array; arrays) {
          if (array.valueType() == type.elemType) {
            /// var[offset] = cache[i];
            emitAssign(af, getIndex(var, offset), reinterpret_cast(type.elemType, array));
            /// offset = offset + 1
            emitAssign(af, offset, lookupOp("+"[], offset, mkInt(1)));
          } else {
            Expr c;
            if (isLiteral(array)) c = array;
            else c = getIndex(cache, mkInt(cacheId ++));
            auto len = getArrayLength(c);
            /// var[offset .. offset + cache[i].length] = cache[i];
            optst(getSliceAssign(mkArraySlice(var, offset, lookupOp("+"[], offset, len)), c.dup)).emitAsm(af);
            /// offset = offset + cache[i].length;
            emitAssign(af, offset, lookupOp("+"[], offset, len));
          }
        }
      });
    }
  }
}

import ast.modules;
static this() {
  IType isArray(IType it) {
    if (auto ar = fastcast!(Array) (it)) return ar.elemType;
    if (auto sa = fastcast!(StaticArray) (it)) return sa.elemType;
    return null;
  }
  bool isExtArray(IType it) { return !!fastcast!(ExtArray) (it); }
  bool isEqual(IType i1, IType i2) {
    return test(resolveType(i1) == resolveType(i2));
  }
  defineOp("~"[], delegate Expr(Expr ex1, Expr ex2) {
    auto cc = fastcast!(ConcatChain) (ex1); // lol
    if (!cc) return null;
    if (!gotImplicitCast(ex2, (IType it) {
      auto base = isArray(it);
      if (!base) return false;
      return test(base == cc.type.elemType);
    })) {
      Expr ex22 = ex2;
      if (!gotImplicitCast(ex22, cc.type.elemType, cc.type.elemType /apply/ &isEqual))
        return null;
      ex2 = ex22;
    }
    return fastalloc!(ConcatChain)(cc.arrays ~ ex2);
  });
  defineOp("~"[], delegate Expr(Expr ex1, Expr ex2) {
    IType base1;
    if (!gotImplicitCast(ex1, (IType it) {
      auto b1 = isArray(it);
      if (b1) base1 = b1;
      return !!b1; 
    })) return null;
    if (!gotImplicitCast(ex2, (IType it) {
      auto b2 = isArray(it);
      if (!b2) return false;
      return test(b2 == base1);
    })) {
      auto ex22 = ex2;
      if (!gotImplicitCast(ex22, base1, base1 /apply/ &isEqual)) return null;
      ex2 = ex22;
    }
    return fastalloc!(ConcatChain)(ex1, ex2);
  });
  defineOp("~"[], delegate Expr(Expr ex1, Expr ex2) {
    auto e1vt = resolveType(ex1.valueType());
    if (!isExtArray(e1vt)) return null;
    auto comparison = fastalloc!(Array)((fastcast!(ExtArray)~ e1vt).elemType);
    if (!gotImplicitCast(ex2, comparison, (IType it) {
      return test(comparison == it);
    })) return null;
    if (!fastcast!(LValue) (ex1)) {
      logln("Cannot concatenate ext+array: ext is not lvalue; cannot invalidate: "[], ex1, ex2);
      fail;
    }
    auto ea = fastcast!(ExtArray)~ e1vt;
    if (ea.freeOnResize) {
      return iparse!(Expr, "concat_into_ext_fOR"[], "tree.expr"[])
                    (`sap!T(&l, r)`,
                    namespace(),
                    "T"[], ea.elemType, "l"[], ex1, "r"[], ex2, "sap"[], sysmod.lookup("append3"[]));
    } else {
      return iparse!(Expr, "concat_into_ext"[], "tree.expr"[])
                    (`sap!T(&l, r)`,
                    namespace(),
                    "T"[], ea.elemType, "l"[], ex1, "r"[], ex2, "sap"[], sysmod.lookup("append2"[]));
    }
  });
  defineOp("~"[], delegate Expr(Expr ex1, Expr ex2) {
    auto e1vt = resolveType(ex1.valueType());
    if (!isExtArray(e1vt)) return null;
    auto et = resolveType((fastcast!(ExtArray)~ e1vt).elemType);
    if (!gotImplicitCast(ex2, et, (IType it) { return !!(it == et); }))
      return null;
    if (!fastcast!(LValue) (ex1)) {
      logln("Cannot concatenate ext+elem: ext is not lvalue; cannot invalidate: "[], ex1, ex2);
      fail;
    }
    auto ea = fastcast!(ExtArray)~ e1vt;
    if (ea.freeOnResize) {
      return iparse!(Expr, "concat_into_ext_fOR_elem"[], "tree.expr"[])
                    (`sap!T(&l, r)`, namespace(),
                    "T"[], resolveType(ea.elemType), "l"[], ex1, "r"[], ex2, "sap"[], sysmod.lookup("append3e"[]));
    } else {
      return iparse!(Expr, "concat_into_ext_elem"[], "tree.expr"[])
                    (`sap!T(&l, r)`, namespace(),
                    "T"[], ea.elemType, "l"[], ex1, "r"[], ex2, "sap"[], sysmod.lookup("append2e"[]));
    }
  });
  defineOp("~"[], delegate Expr(Expr ex1, Expr ex2) {
    auto e1vt = resolveType(ex1.valueType());
    if (!isExtArray(e1vt)) return null;
    auto et = resolveType((fastcast!(ExtArray)~ e1vt).elemType);
    if (!gotImplicitCast(ex2, (IType it) {
      auto sa = fastcast!(StaticArray) (it);
      return sa && resolveType(sa.elemType) == et;
    }))
      return null;
    if (!fastcast!(LValue) (ex1)) {
      logln("Cannot concatenate ext+elem x ?: ext is not lvalue; cannot invalidate: "[], ex1, ex2);
      fail;
    }
    auto ea = fastcast!(ExtArray)~ e1vt;
    if (ea.freeOnResize) {
      return fastalloc!(StatementAndExpr)(
        iparse!(Statement, "concat_into_ext_fOR_static_array"[], "tree.stmt"[])
               (`for auto e <- r l = sap!T(&l, e);`, namespace(),
                "T"[], ea.elemType, "l"[], ex1, "r"[], ex2, "sap"[], sysmod.lookup("append3e"[]))
        , ex1
      );
    } else {
      return fastalloc!(StatementAndExpr)(
        iparse!(Statement, "concat_into_ext_static_array"[], "tree.stmt"[])
               (`for auto e <- r l = sap!T(&l, e);`, namespace(),
                "T"[], ea.elemType, "l"[], ex1, "r"[], ex2, "sap"[], sysmod.lookup("append2e"[]))
        , ex1
      );
    }
  });
  defineOp("~"[], delegate Expr(Expr ex1, Expr ex2) {
    // logln("op: concat"[]);
    // logln("ex1: "[], ex1.valueType());
    // logln("ex2: "[], ex2.valueType());
    // fail;
    // throw new Exception("Concatenation error"[]);
    throw new Exception(Format("Concatenation error: incompatible types: "[],
      ex1.valueType(), " and "[], ex2.valueType()));
    // return null;
  });
  // fold string concats
  foldopt ~= delegate Itr(Itr it) {
    auto cc = fastcast!(ConcatChain) (it);
    if (!cc) return null;
    if (cc.type != Single!(Array, Single!(Char))) return null;
    string res;
    foreach (ex2; cc.arrays) {
      ex2 = foldex(ex2);
      if (auto se = fastcast!(StringExpr) (ex2)) res ~= se.str;
      else return null;
    }
    return fastalloc!(StringExpr)(res);
  };
}

import ast.casting;
Object gotConcatChain(ref string text, ParseCb cont, ParseCb rest) {
  Expr op, op2;
  auto t2 = text;
  IType elemtype;
  if (!cont(t2, &op)) return null;
  auto first = op;
  try {
    retry:
    auto t3 = t2;
    if (t3.accept("~="[]) && rest(t3, "tree.expr"[], &op2)) {
      op = lookupOp("~="[], op, op2);
      if (!op) return null;
      t2 = t3;
      goto retry;
    }
    if (t2.accept("~"[]) && cont(t2, &op2)) {
      op = lookupOp("~"[], op, op2);
      if (!op) return null;
      goto retry;
    }
  } catch (Exception ex) {
    t2.failparse("Could not concatenate: "[], ex);
  }
  if (op is first) return null;
  text = t2;
  return fastcast!(Object)~ op;
}
mixin DefaultParser!(gotConcatChain, "tree.expr.arith.concat"[], "305"[]);
