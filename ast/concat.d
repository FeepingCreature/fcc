module ast.concat;

import
  ast.base, ast.parse, ast.arrays, ast.static_arrays, ast.int_literal, ast.casting,
  ast.vardecl, ast.scopes, ast.aggregate, ast.namespace, ast.index, ast.tuples, ast.pointer,
  ast.assign, ast.opers, ast.slice, ast.literal_string, ast.literals, ast.fold, tools.base: take;

class ConcatChain : Expr {
  Array type;
  Expr[] arrays;
  bool[] doIownThisArray; // do I have to free it after I've been evaluated?
  this(Expr[] exprs...) {
    if (!exprs.length) assert(false); // null type?!
    auto base = exprs.take();
    auto bvt = resolveType(base.valueType());
    if (auto sa = fastcast!(StaticArray)(bvt)) {
      type = fastalloc!(Array)(sa.elemType);
      if (!type) fail(Format(sa, " elemtype is null - what "));
    } else {
      type = fastcast!(Array) (bvt);
      if (!type) fail(Format(bvt, " is not array or static array! "[]));
    }
    addArray(base);
    foreach (expr; exprs)
      addArray(expr);
  }
  override ConcatChain dup() {
    auto arrays = arrays.dup;
    foreach (ref ex; arrays) ex = ex.dup;
    auto res = new ConcatChain(arrays);
    res.doIownThisArray = doIownThisArray.dup;
    return res;
  }
  mixin defaultIterate!(arrays);
  Expr collapse() {
    if (type == Single!(Array, Single!(Char))) {
      string res;
      foreach (ex2; arrays) {
        if (auto se = fastcast!(StringExpr) (.collapse(ex2))) res ~= se.str;
        else return this;
      }
      return fastalloc!(StringExpr)(res);
    }
    return this;
  }
  void addArray(Expr ex, bool freeAfterEvaluate = false) {
    Expr nuArray;
    if (fastcast!(StaticArray)~ ex.valueType()) nuArray = staticToArray(ex);
    else nuArray = ex;
    
    {
      auto backup = nuArray;
      nuArray = .collapse(nuArray);
      freeAfterEvaluate &= nuArray is backup; // otherwise we just optimized away something that was PROBABLY an allocation TODO sanity check
    }
    if (arrays.length) {
      auto se1 = fastcast!(StringExpr) (arrays[$-1]);
      auto se2 = fastcast!(StringExpr) (nuArray);
      if (se1 && se2) {
        arrays[$-1] = mkString(se1.str~se2.str);
        return;
      }
    }
    arrays ~= nuArray;
    doIownThisArray ~= freeAfterEvaluate;
  }
  override {
    IType valueType() { return type; }
    string toString() {
      auto mod = fastcast!(Module) (current_module());
      if (mod !is sysmod) return Format("~", arrays, " <", doIownThisArray, ">");
      return Format("~", arrays);
    }
    void emitLLVM(LLVMFile lf) {
      mixin(mustOffset("1"));
      
      string lit;
      bool isLiteral(Expr ex) {
        if (auto se = fastcast!(StringExpr) (ex)) {
          lit = se.str;
          return true;
        }
        return false;
      }
      
      int cacheNeeded;
      foreach (ref array; arrays) {
        if (array.valueType() != type.elemType && !isLiteral(array)) cacheNeeded ++;
      }
        
      auto sa = fastalloc!(StaticArray)(valueType(), cacheNeeded);
      auto
        offset = fastalloc!(LLVMRef)(Single!(SysInt)),
        total  = fastalloc!(LLVMRef)(Single!(SysInt)),
        cache  = fastalloc!(LLVMRef)(sa),
        res    = fastalloc!(LLVMRef)(type);
      
      int known_len;
      foreach (array; arrays) {
        if (array.valueType() == type.elemType) { known_len ++; }
        else if (isLiteral(array)) {
          known_len += lit.length;
        }
      }
      
      res   .allocate(lf);
      offset.allocate(lf);
      total .allocate(lf);
      cache .allocate(lf);
      
      offset.begin(lf); scope(success) offset.end(lf);
      // initialize to 0
      emitAssign(lf, offset, fastalloc!(ZeroInitializer)(Single!(SysInt)));
      total.begin(lf); scope(success) total.end(lf);
      emitAssign(lf, total, mkInt(known_len));
      int cacheId = 0;
      cache.begin(lf); scope(success) cache.end(lf);
      foreach (array; arrays) {
        if (array.valueType() == type.elemType) continue;
        if (isLiteral(array)) continue;
        // cache[i] = array
        auto cachepos = getIndex(cache, mkInt(cacheId++));
        emitAssign(lf, cachepos, array);
        // total = total + cache[i].length
        emitAssign(lf, total, lookupOp("+"[], total, getArrayLength(cachepos)));
      }
      res.begin(lf); scope(success) res.end(lf);
      iparse!(Statement, "alloc_array"[], "tree.semicol_stmt.assign"[])
      (
        "res = new T[] total"[],
        "res"[], res, "T"[], type.elemType,
        "total"[], total
      ).emitLLVM(lf);
      cacheId = 0;
      foreach (i, array; arrays) {
        if (array.valueType() == type.elemType) {
          /// res[offset] = cache[i];
          emitAssign(lf, getIndex(res, offset), reinterpret_cast(type.elemType, array));
          /// offset = offset + 1
          emitAssign(lf, offset, lookupOp("+"[], offset, mkInt(1)));
        } else {
          Expr c;
          if (isLiteral(array)) c = array;
          else c = getIndex(cache, mkInt(cacheId ++));
          auto len = getArrayLength(c);
          auto end = .collapse(lookupOp("+", offset, len));
          /// res[offset .. offset + cache[i].length] = cache[i];
          auto stmt = getSliceAssign(mkArraySlice(res, offset, end), c);
          opt(stmt);
          stmt.emitLLVM(lf);
          /// offset = offset + cache[i].length;
          emitAssign(lf, offset, end);
          /// cache[i].free;
          auto mod = fastcast!(Module) (current_module());
          if (mod !is sysmod && doIownThisArray[i]) { // no var.free in sysmod because hax
            freeVar(c).emitLLVM(lf);
          }
        }
      }
      res.emitLLVM(lf);
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
    auto ea = fastcast!(ExtArray) (e1vt);
    if (!ea) return null;
    auto et = resolveType(ea.elemType);
    if (!gotImplicitCast(ex2, et, (IType it) { return !!(it == et); }))
      return null;
    if (!fastcast!(LValue) (ex1)) {
      logln("Cannot concatenate ext+elem: ext is not lvalue; cannot invalidate: "[], ex1, ex2);
      fail;
    }
    if (ea.freeOnResize) {
      return iparse!(Expr, "concat_into_ext_fOR_elem"[], "tree.expr"[])
                    (`sap!T tup`, namespace(),
                    "T"[], resolveType(ea.elemType), "tup"[], mkTupleExpr(fastalloc!(RefExpr)(fastcast!(CValue)(ex1)), ex2), "sap"[], sysmod.lookup("append3e"[]));
    } else {
      return iparse!(Expr, "concat_into_ext_elem"[], "tree.expr"[])
                    (`sap!T tup`, namespace(),
                    "T"[], ea.elemType, "tup"[], mkTupleExpr(fastalloc!(RefExpr)(fastcast!(CValue)(ex1)), ex2), "sap"[], sysmod.lookup("append2e"[]));
    }
  });
  defineOp("~"[], delegate Expr(Expr ex1, Expr ex2) {
    auto e1vt = resolveType(ex1.valueType());
    auto ea = fastcast!(ExtArray) (e1vt);
    if (!ea) return null;
    auto comparison = fastalloc!(Array)(ea.elemType);
    auto ex2test = ex2;
    if (!gotImplicitCast(ex2, comparison, (IType it) {
      return test(comparison == it);
    })) return null;
    if (!fastcast!(LValue) (ex1)) {
      logln("Cannot concatenate ext+array: ext is not lvalue; cannot invalidate: "[], ex1, ex2);
      fail;
    }
    if (ea.freeOnResize) {
      return iparse!(Expr, "concat_into_ext_fOR"[], "tree.expr"[])
                    (`sap!T tup`,
                    namespace(),
                    "T"[], ea.elemType, "tup"[], mkTupleExpr(fastalloc!(RefExpr)(fastcast!(CValue)(ex1)), ex2), "sap"[], sysmod.lookup("append3"[]));
    } else {
      return iparse!(Expr, "concat_into_ext"[], "tree.expr"[])
                    (`sap!T tup`,
                    namespace(),
                    "T"[], ea.elemType, "tup"[], mkTupleExpr(fastalloc!(RefExpr)(fastcast!(CValue)(ex1)), ex2), "sap"[], sysmod.lookup("append2"[]));
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
               (`for auto __e <- r l = sap!T(&l, __e);`, namespace(),
                "T", ea.elemType, "l", ex1, "r", ex2, "sap", sysmod.lookup("append3e"[]))
        , ex1
      );
    } else {
      return fastalloc!(StatementAndExpr)(
        iparse!(Statement, "concat_into_ext_static_array"[], "tree.stmt"[])
               (`for auto __e <- r l = sap!T(&l, __e);`, namespace(),
                "T", ea.elemType, "l", ex1, "r", ex2, "sap", sysmod.lookup("append2e"[]))
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
    // TODO better error if ex1 is not an array
    throw new Exception(Format("Concatenation error: incompatible types: "[],
      ex1.valueType(), " and "[], ex2.valueType()));
    // return null;
  });
}
