module ast.tuple_access;

import ast.base, ast.tuples, ast.structure;

Expr mkTupleIndexAccess(Expr tuple, int pos) {
  auto wrapped = (fastcast!(Tuple)~ tuple.valueType()).wrapped;
  
  MemberAccess_Expr res;
  if (fastcast!(LValue)~ tuple) res = new MemberAccess_LValue;
  else res = new MemberAccess_Expr;
  res.base = reinterpret_cast(wrapped, tuple);
  
  auto temps = wrapped.selectMap!(RelMember, "$");
  res.stm = temps[pos];
  
  auto types = (fastcast!(Tuple)~ tuple.valueType()).types();
  return foldex(reinterpret_cast(types[pos], res));
}

Expr[] getTupleEntries(Expr tuple) {
  auto tt = fastcast!(Tuple)~ tuple.valueType();
  assert(!!tt);
  auto count = tt.types.length;
  Expr[] res;
  for (int i = 0; i < count; ++i)
    res ~= mkTupleIndexAccess(tuple, i);
  return res;
}

import ast.parse, ast.fold, ast.int_literal, ast.namespace;
Object gotTupleIndexAccess(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto tup = fastcast!(Tuple)~ ex.valueType();
    if (!tup) return null;
    int count;
    tup.wrapped.select((string, RelMember rm) { count ++; });
    /// 2.1
    if (count <= 1) return null; // resolve ambiguity with array index
    auto t2 = text;
    Expr index;
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(new LengthOverride(backup, mkInt(count)));
    
    if (
      !rest(t2, "tree.expr", &index) ||
      !gotImplicitCast(index, (IType it) { return test(Single!(SysInt) == it); }) ||
      !t2.accept("]")) return null;
    text = t2;
    index = foldex(index);
    auto ie = fastcast!(IntExpr)~ index;
    if (!ie) {
      text.setError(index, " could not be simplified to an int in tuple index access");
      return null;
    }
    if (ie.num < 0 || ie.num !< count)
      text.failparse(ie.num, " out of bounds for tuple access");
    return fastcast!(Object)~ mkTupleIndexAccess(ex, ie.num);
  };
}
mixin DefaultParser!(gotTupleIndexAccess, "tree.rhs_partial.tuple_index_access", null, "[");

import ast.iterator, ast.casting;
Object gotTupleSliceExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto tup = fastcast!(Tuple)~ ex.valueType();
    if (!tup) return null;
    int count;
    tup.wrapped.select((string, RelMember rm) { count ++; });
    /// 2.1
    if (count <= 1) return null;
    auto t2 = text;
    Expr range;
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(new LengthOverride(backup, mkInt(count)));
    
    if (!rest(t2, "tree.expr", &range) ||
        !gotImplicitCast(range, (IType it) { return test(fastcast!(RangeIsh)~ it); }) ||
        !t2.accept("]")) return null;
    auto rish = fastcast!(RangeIsh)~ range.valueType(),
      from = rish.getPos(range),
      to   = rish.getEnd(range);
    text = t2;
    auto ifrom = fastcast!(IntExpr)~ fold(from), ito = fastcast!(IntExpr)~ fold(to);
    text.passert(ifrom && ito, "fail");
    auto start = tup.wrapped.selectMember(ifrom.num).offset;
    auto restype = mkTuple(tup.wrapped.slice(ifrom.num, ito.num).types);
    auto res = iparse!(Expr, "tuple_slice", "tree.expr")
                      (`*restype*:(void*:&lv + base)`,
                       "restype", restype, "lv", fastcast!(LValue)~ ex,
                       "base", mkInt(start));
    return fastcast!(Object)~ res;
  };
}
mixin DefaultParser!(gotTupleSliceExpr, "tree.rhs_partial.tuple_slice", null, "[");

class WithSpace : Namespace {
  Namespace ns; RelNamespace rns;
  Expr ctx;
  this(Expr ex) {
    ctx = ex;
    sup = namespace();
    rns = fastcast!(RelNamespace)~ ex.valueType();
    if (auto srns = cast(SemiRelNamespace) ex.valueType())
      rns = srns.resolve();
    ns = fastcast!(Namespace)~ ex;
  }
  override {
    string mangle(string name, IType type) { assert(false); }
    Stuple!(IType, string, int)[] stackframe() { assert(false); }
    Object lookup(string name, bool local = false) {
      if (rns)
        if (auto res = rns.lookupRel(name, ctx)) return res;
      if (ns)
        if (auto res = ns.lookup(name, local)) return res;
      return sup.lookup(name, local);
    }
  }
}

import ast.iterator, ast.casting, ast.pointer;
Object gotWithTupleExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    {
      auto t2 = text;
      if (!t2.accept("(")) return null;
    }
    while (fastcast!(Pointer)~ ex.valueType())
      ex = new DerefExpr(ex);
    
    auto ns = fastcast!(Namespace)~ ex.valueType();
    auto rns = fastcast!(RelNamespace)~ ex.valueType();
    if (!ns && !rns)
      text.failparse("Not a [rel]namespace: ", ex.valueType());
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(new WithSpace(ex));
    Object res;
    if (!rest(text, "tree.expr _tree.expr.arith", &res))
      text.failparse("Couldn't get with-tuple expr");
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
    if (!it || !fastcast!(Tuple) (it)) return null;
    if (auto tup = fastcast!(Tuple)~ ex.valueType()) {
      if ((fastcast!(Tuple)~ it).types.length != tup.types.length)
        return null;
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
