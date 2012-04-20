module ast.tuples;

import ast.base, ast.structure, ast.namespace, ast.casting, ast.opers;

/++
  1. A tuple behaves like a struct
  2. A tuple accepts index and slice notation.
  3. There is no such thing as a size-one tuple.
  4. A tuple is matched via '()' and ','.
++/

class Tuple : Type, RelNamespace {
  /// 1.
  Structure wrapped;
  NSCache!(IType) typecache;
  NSCache!(int) offsetcache;
  IType[] types() { return wrapped.selectMap!(RelMember, "$.type")(&typecache); }
  int[] offsets() { return wrapped.selectMap!(RelMember, "$.offset")(&offsetcache); }
  override {
    bool isTempNamespace() { return false; }
    Object lookupRel(string str, Expr base, bool isDirectLookup = true) {
      int idx;
      if (readIndexShorthand(str, idx))
        return fastcast!(Object) (lookupOp("index"[], base, mkInt(idx)));
      return null;
    }
    int size() { return wrapped.size; }
    bool isComplete() { return wrapped.isComplete; }
    string mangle() { return "tuple_"~wrapped.mangle(); }
    ubyte[] initval() { return wrapped.initval(); }
    string toString() { string res; foreach (i, ty; types()) { if (i) res ~= ", "; res ~= Format(ty); } return "(" ~ res ~ ")"; }
    int opEquals(IType it) {
      if (!super.opEquals(it)) return false;
      it = resolveType(it);
      auto tup = fastcast!(Tuple) (it);
      assert(!!tup);
      auto types1 = types(), types2 = tup.types();
      if (types1.length != types2.length) return false;
      for (int i = 0; i < types1.length; ++i) {
        if (types1[i] != types2[i]) return false;
      }
      return true;
    }
  }
}

Object gotBraceExpr(ref string text, ParseCb cont, ParseCb rest) {
  Object obj; // exclusively for non-exprs.
  auto t2 = text;
  bool globmode;
  if (!t2.accept("("[])) {
    if (t2.accept("$"[])) globmode = true;
    else return null;
  }
  if (!rest(t2, "tree.expr"[], &obj))
    return null;
  if (!(globmode ^ !fastcast!(Expr) (obj)))
    return null;
  if (globmode || t2.accept(")"[])) {
    text = t2;
    return obj;
  } else {
    if (!t2.accept(","[]))
      t2.setError("Failed to match single-tuple"[]);
    return null;
  }
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces"[], "6"[]);

Tuple mkTuple(IType[] types...) {
  foreach (type; types) if (Single!(Void) == type) {
    logln("Cannot make tuple: must not contain void, "[], types);
    fail;
  }
  auto tup = new Tuple;
  New(tup.wrapped, cast(string) null);
  tup.wrapped.packed = true;
  foreach (i, type; types)
    fastalloc!(RelMember)(qformat("tuple_member_"[], i), type, tup.wrapped);
  return tup;
}

Object gotTupleType(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  IType[] types;
  if (t2.bjoin(
        !!rest(t2, "type"[], &ty),
        t2.accept(","[]),
        { types ~= ty; }
      ) &&
      t2.accept(")"[])
    ) {
    if (!types.length) { text = t2; return mkTuple(); } // templateFoo!()
    text = t2;
    return mkTuple(types);
  } else return null;
}
mixin DefaultParser!(gotTupleType, "type.tuple"[], "37"[], "("[]);

import ast.assign;

class RefTuple : MValue {
  IType baseTupleType;
  MValue[] mvs;
  mixin defaultIterate!(mvs);
  IType[] types() { return (fastcast!(Tuple) (baseTupleType)).types(); }
  Expr[] getAsExprs() {
    Expr[] exprs;
    foreach (mv; mvs) exprs ~= mv;
    return exprs;
  }
  this(MValue[] mvs...) {
    this.mvs = mvs.dup;
    baseTupleType = mkTupleValueExpr(getAsExprs()).valueType();
  }
  override {
    RefTuple dup() {
      auto newlist = mvs.dup;
      foreach (ref entry; newlist) entry = entry.dup;
      return fastalloc!(RefTuple)(newlist);
    }
    IType valueType() { return baseTupleType; }
    void emitAsm(AsmFile af) {
      mkTupleValueExpr(getAsExprs).emitAsm(af);
    }
    string toString() {
      return Format("reftuple("[], mvs, ")"[]);
    }
    void emitAssignment(AsmFile af) {
      mixin(mustOffset("-valueType().size"[]));
      auto tup = fastcast!(Tuple)~ baseTupleType;
      
      auto offsets = tup.offsets();
      int data_offs;
      foreach (i, target; mvs) {
        if (offsets[i] != data_offs) {
          assert(offsets[i] > data_offs);
          af.sfree(offsets[i] - data_offs);
        }
        mixin(mustOffset("-target.valueType().size"[]));
        target.emitAssignment(af);
        data_offs += target.valueType().size;
      }
      if (tup.size != data_offs)
        af.sfree(tup.size - data_offs);
    }
  }
}

import ast.aggregate;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto mae = fastcast!(MemberAccess_Expr) (it);
    if (!mae) return null;
    auto rc = fastcast!(RCE)~ mae.base;
    if (!rc) return null;
    auto rt = fastcast!(RefTuple) (rc.from);
    auto str = fastcast!(Structure)~ rc.to;
    if (!rt || !str) return null;
    retry:
    // logln("member access to a "[], rc, " - "[], mae.stm);
    auto mbs = str.members();
    if (mbs.length > 1 && rt.mvs.length == 1) {
      rt = fastcast!(RefTuple) (rt.mvs[0]);
      if (rt) goto retry;
      else return null; // TODO: I don't get this. 
    }
    if (!rt || rt.mvs.length != mbs.length) {
      logln("ref tuple not large enough for this cast! "[]);
      logln(rt, " but "[], mbs);
      fail;
    }
    int offs = -1;
    foreach (id, entry; mbs) if (entry is mae.stm) { offs = id; break; }
    if (offs == -1) fail();
    return fastcast!(Itr) (rt.mvs[offs]);
  };
  // translate mvalue tuple assignment into sequence of separate assignments
  foldopt ~= delegate Itr(Itr it) {
    auto am = fastcast!(AssignmentM) (it);
    if (!am) return null;
    auto rt1 = fastcast!(RefTuple) (am.target);
    if (!rt1) return null;
    Expr value = am.value; Statement stmt;
    if (auto sam = fastcast!(StatementAndMValue) (value)) {
      stmt = sam.first;
      value = sam.second;
    }
    auto rt2 = fastcast!(RefTuple) (value);
    if (!rt2) return null;
    if (rt1.mvs.length != rt2.mvs.length) fail;
    
    try {
      Statement[] stmts;
      if (stmt) stmts ~= stmt;
      for (int i = 0; i < rt1.mvs.length; ++i) {
        Expr left = rt1.mvs[i], right = rt2.mvs[i];
        if (auto lam = fastcast!(LValueAsMValue) (left)) left = lam.sup;
        if (auto lam = fastcast!(LValueAsMValue) (right)) right = lam.sup;
        stmts ~= mkAssignment(left, right);
      }
      // return fastalloc!(AggrStatement)(stmts);
      // this breaks (a, b) = (b, a).
      // Don't actually do it, but act like we did so we get the benefit
      // of the self-assignment error which is neat.
      return null;
    } catch (SelfAssignmentException) {
      throw fastalloc!(ParseEx)(reverseLookupPos(am.line, 0, am.name), "self-assignment detected"[]);
    }
  };
}

Expr mkTupleValueExpr(Expr[] exprs...) {
  auto tup = mkTuple(exprs /map/ (Expr ex) { return ex.valueType(); });
  return fastalloc!(RCE)(tup, fastalloc!(StructLiteral)(tup.wrapped, exprs.dup, tup.offsets));
}

class LValueAsMValue : MValue {
  LValue sup;
  mixin MyThis!("sup"[]);
  mixin defaultIterate!(sup);
  override {
    LValueAsMValue dup() { return fastalloc!(LValueAsMValue)(sup.dup); }
    string toString() { return Format("lvtomv("[], sup, ")"[]); }
    void emitAsm(AsmFile af) { sup.emitAsm(af); }
    IType valueType() { return sup.valueType(); }
    import ast.assign;
    void emitAssignment(AsmFile af) {
      (fastalloc!(Assignment)(
        sup,
        fastalloc!(Placeholder)(sup.valueType()),
        false, true
      )).emitAsm(af);
    }
  }
}

extern(C) IType resolveTup(IType it, bool onlyIfChanged = false) {
  auto res = resolveType(it);
  if (auto tup = fastcast!(Tuple) (res)) {
    auto types = tup.types();
    if (types.length == 1) return types[0];
  }
  if (auto rt = fastcast!(RefTuple) (res)) {
    auto types = rt.types();
    if (types.length == 1) return types[0];
  }
  if (onlyIfChanged) return null;
  return res;
}

static this() {
  forcedConversionDg = forcedConversionDg /apply/ delegate Expr(Expr delegate(Expr) prev, Expr ex) {
    if (prev) ex = prev(ex);
    if (auto newtype = resolveTup(ex.valueType(), true)) {
      return forcedConvert(reinterpret_cast(newtype, ex));
    }
    return ex;
  };
  forcedTypeConversionDg = forcedTypeConversionDg /apply/ delegate IType(IType delegate(IType) prev, IType it) {
    if (prev) it = prev(it);
    if (auto newtype = resolveTup(it, true)) return newtype;
    return it;
  };
}

Expr mkTupleExpr(Expr[] exprs...) {
  bool allMValues = true;
  MValue[] arr;
  MValue toMValue(Expr ex) {
    if (auto mv = fastcast!(MValue) (ex)) return mv;
    if (auto lv = fastcast!(LValue) (ex)) return fastalloc!(LValueAsMValue)(lv);
    return null;
  }
  // first check if all are mvalues even without the foldex
  foreach (ex; exprs) {
    if (auto mv = toMValue (ex)) arr ~= mv;
    else { allMValues = false; break; }
  }
  if (!allMValues) {
    arr.length = 0;
    allMValues = true;
    foreach (ref ex; exprs) {
      ex = foldex(ex);
      if (auto mv = toMValue (ex)) arr ~= mv;
      else { allMValues = false; break; }
    }
  }
  if (allMValues) return fastalloc!(RefTuple)(arr);
  else return mkTupleValueExpr(exprs);
}

/// 4.
import ast.math: AsmFloatBinopExpr;
Object gotTupleExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr[] exprs;
  auto t2 = text;
  if (t2.accept(")"[])) {
    text = t2;
    // lol wat
    return fastcast!(Object)~ mkTupleExpr();
  }
  while (true) {
    Expr ex;
    if (exprs.length > 1) {
      if (!t2.accept(","[]))
        t2.failparse("tuple failed; comma expected"[]);
      if (!rest(t2, "tree.expr"[], &ex))
        t2.failparse("tuple failed"[]);
    } else if (exprs.length) {
      if (!t2.accept(","[]))
        return null;
      if (!rest(t2, "tree.expr"[], &ex))
        return null;
    } else {
      if (!rest(t2, "tree.expr"[], &ex))
        return null;
    }
    exprs ~= ex;
    if (t2.accept(")"[])) break;
  }
  text = t2;
  return fastcast!(Object) (mkTupleExpr(exprs));
}
mixin DefaultParser!(gotTupleExpr, "tree.expr.tuple"[], "60"[], "("[]);

import ast.fold, ast.int_literal;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (auto rt = fastcast!(RefTuple) (ex)) {
      if (rt.mvs.length == 1) {
        if (auto lvamv = fastcast!(LValueAsMValue) (rt.mvs[0]))
          return lvamv.sup;
        return rt.mvs[0];
      }
    }
    return null;
  };
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb cont, ParseCb rest) {
    auto t2 = text;
    Expr len;
    if (!t2.accept("["[])) return null;
    
    auto tup = fastcast!(Tuple) (cur);
    if (!tup)
      return null;
    
    if (!rest(t2, "tree.expr"[], &len)) return null;
    if (!t2.accept("]"[]))
      t2.failparse("Expected closing ']' for tuple index access"[]);
    
    auto types = tup.types();
    if (!types.length) return null; // cannot possibly mean a type-tuple tuple access
    
    auto backup_len = len;
    if (!gotImplicitCast(len, (IType it) { return test(Single!(SysInt) == it); }))
      t2.failparse("Need int for tuple index access, not "[], backup_len);
    opt(len);
    len = foldex(len);
    if (auto ie = fastcast!(IntExpr) (len)) {
      text = t2;
      if (ie.num >= types.length) {
        text.failparse(ie.num, " too large for tuple of "[], types.length, "!"[]);
      }
      return types[ie.num];
    } else
      t2.failparse("Need foldable constant for tuple index access, not "[], len);
  };
}
