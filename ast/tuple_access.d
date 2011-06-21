module ast.tuple_access;

import ast.base, ast.tuples, ast.structure;

Expr mkTupleIndexAccess(Expr tuple, int pos) {
  if (auto rt = fastcast!(RefTuple) (tuple)) {
    return rt.mvs[pos];
  }
  auto wrapped = (fastcast!(Tuple)~ tuple.valueType()).wrapped;
  
  MemberAccess_Expr res;
  if (fastcast!(LValue)~ tuple) res = new MemberAccess_LValue;
  else res = new MemberAccess_Expr;
  res.base = reinterpret_cast(wrapped, tuple);
  
  auto temps = wrapped.selectMap!(RelMember, "$");
  res.stm = temps[pos];
  
  auto types = (fastcast!(Tuple)~ tuple.valueType()).types();
  return reinterpret_cast(types[pos], res);
}

Expr[] getTupleEntries(Expr tuple) {
  auto tt = fastcast!(Tuple)~ tuple.valueType();
  if (!tt) return null;
  auto count = tt.types.length;
  Expr[] res;
  for (int i = 0; i < count; ++i)
    res ~= mkTupleIndexAccess(tuple, i);
  return res;
}

import ast.parse, ast.fold, ast.int_literal, ast.namespace, ast.opers;
static this() {
  defineOp("index", delegate Expr(Expr e1, Expr e2) {
    Tuple tup;
    if (!gotImplicitCast(e1, (IType it) {
      tup = fastcast!(Tuple) (it);
      return tup && tup.types.length > 1; // resolve ambiguity with array index
    }))
      return null;
    int count;
    tup.wrapped.select((string, RelMember rm) { count ++; }, &tup.wrapped.rmcache);
    /// 2.1
    if (!gotImplicitCast(e2, (IType it) { return test(Single!(SysInt) == it); }))
      return null;
    e2 = foldex(e2);
    auto ie = fastcast!(IntExpr) (e2);
    if (!ie) {
      return null;
      // throw new Exception(Format(e2, " could not be simplified to an int in tuple index access"));
    }
    if (ie.num < 0 || ie.num !< count)
      throw new Exception(Format(ie.num, " out of bounds for tuple access"));
    return fastcast!(Expr) (mkTupleIndexAccess(e1, ie.num));
  });
  defineOp("length", delegate Expr(Expr ex) {
    Tuple tup;
    if (!gotImplicitCast(ex, (IType it) {
      tup = fastcast!(Tuple) (it);
      return tup && tup.types.length > 1; // resolve ambiguity with array length
    }))
      return null;
    return mkInt(tup.types.length);
  });
}

import ast.iterator, ast.casting;
static this() {
  defineOp("index", delegate Expr(Expr e1, Expr e2) {
    auto tup = fastcast!(Tuple) (e1.valueType());
    if (!tup) return null;
    int count;
    tup.wrapped.select((string, RelMember rm) { count ++; }, &tup.wrapped.rmcache);
    /// 2.1
    if (count <= 1) return null;
    if (!gotImplicitCast(e2, (IType it) { return test(fastcast!(RangeIsh) (it)); }))
      return null;
    
    auto rish = fastcast!(RangeIsh) (e2.valueType()),
      from = rish.getPos(e2),
      to   = rish.getEnd(e2);
    auto ifrom = fastcast!(IntExpr) (fold(from)), ito = fastcast!(IntExpr) (fold(to));
    if (!ifrom || !ito) fail("fail");
    auto start = tup.wrapped.selectMember(ifrom.num).offset;
    auto restype = mkTuple(tup.wrapped.slice(ifrom.num, ito.num).types);
    auto res = iparse!(Expr, "tuple_slice", "tree.expr")
                      (`*restype*:(void*:&lv + base)`,
                       "restype", restype, "lv", fastcast!(LValue)~ e1,
                       "base", mkInt(start));
    return res;
  });
}

class WithSpace : Namespace {
  Object[] spaces;
  Expr[] values;
  this(Expr ex) {
    sup = namespace();
    spaces ~= fastcast!(Object) (ex.valueType());
    values ~= ex;
  }
  this(Object[] spaces, Expr[] values) {
    sup = namespace();
    this.spaces = spaces;
    this.values = values;
  }
  override {
    string mangle(string name, IType type) { assert(false); }
    Stuple!(IType, string, int)[] stackframe() { assert(false); }
    Object lookup(string name, bool local = false) {
      foreach (i, space; spaces) {
        auto rns = fastcast!(RelNamespace) (space);
        
        if (!rns) 
          if (auto srns = fastcast!(SemiRelNamespace) (space))
            rns = srns.resolve();
        
        if (auto srns = fastcast!(SemiRelNamespace) (rns))
          rns = srns.resolve();
        
        if (rns)
          if (auto res = rns.lookupRel(name, values[i])) return res;
        
        if (auto ns = fastcast!(Namespace) (space))
          if (auto res = ns.lookup(name, local)) return res;
      }
      return sup.lookup(name, local);
    }
  }
}

import ast.iterator, ast.casting, ast.pointer, ast.vardecl;
Object gotWithTupleExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Object obj) {
    {
      auto t2 = text;
      if (!t2.accept("(")) return null;
    }
    auto ex = fastcast!(Expr) (obj);
    if (ex)
      while (fastcast!(Pointer) (resolveType(ex.valueType())))
        ex = new DerefExpr(ex);
    
    if (auto it = fastcast!(IType) (obj))
      obj = fastcast!(Object) (resolveType(it));
    
    Object[] spaces;
    Expr[] values;
    
    if (ex) {
      Expr ex2 = lvize(ex);
      gotImplicitCast(ex2, (Expr ex) {
        auto it = ex.valueType();
        if (fastcast!(Namespace) (it) || fastcast!(RelNamespace) (it) || fastcast!(SemiRelNamespace) (it)) {
          spaces ~= fastcast!(Object) (it);
          values ~= ex;
        }
        return false;
      });
    } else {
      if (auto ns = fastcast!(Namespace) (obj)) {
        spaces ~= obj; values ~= null;
      } else if (auto rn = fastcast!(RelNamespace) (obj)) {
        spaces ~= obj; values ~= null;
      }
    }
    
    if (!spaces.length)
      if (ex)
        text.failparse("Not a [rel]namespace: type ", ex.valueType());
      else
        text.failparse("Not a [rel]namespace: obj ", obj.classinfo.name, ": ", obj);
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(new WithSpace(spaces, values));
    
    Object res;
    if (!rest(text, "tree.expr _tree.expr.arith", &res) && !rest(text, "cond", &res))
      text.failparse("Couldn't get with-tuple expr");
    if (auto rt = fastcast!(RefTuple) (res)) if (rt.mvs.length == 1) {
      auto lv2mv = fastcast!(LValueAsMValue) (rt.mvs[0]);
      if (lv2mv) return fastcast!(Object) (lv2mv.sup);
      return fastcast!(Object) (rt.mvs[0]);
    }
    return res;
  };
}
mixin DefaultParser!(gotWithTupleExpr, "tree.rhs_partial.withtuple", null, ".");

static this() {
  /// 3.
  implicits ~= delegate Expr(Expr ex) {
    auto tup = fastcast!(Tuple)~ ex.valueType();
    if (!tup) return null;
    if (tup.types.length != 1) return null;
    auto res = mkTupleIndexAccess(ex, 0);
    return res;
  };
  // cast into tuples
  implicits ~= delegate void(Expr ex, IType it, void delegate(Expr) dg) {
    if (!it || !fastcast!(Tuple) (it)) return;
    if (auto tup = fastcast!(Tuple)~ ex.valueType()) {
      if ((fastcast!(Tuple)~ it).types.length != tup.types.length)
        return;
      auto exprs = getTupleEntries(ex);
      Expr[] stack;
      Expr[][] casts;
      foreach (entry; exprs) {
        stack ~= entry;
        casts ~= getAllImplicitCasts(entry);
      }
      auto offs = new int[exprs.length];
      int inc(int i) {
        stack[i] = casts[i][offs[i]++];
        if (offs[i] == casts[i].length) offs[i] = 0;
        return offs[i];
      }
      while (true) {
        int i;
        while (i < exprs.length && !inc(i)) i++;
        if (i == exprs.length) break;
        auto t = mkTupleExpr(stack);
        if (it == t.valueType()) dg(t);
      }
    }
  };
}
