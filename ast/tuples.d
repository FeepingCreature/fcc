module ast.tuples;

import ast.base, ast.structure, ast.namespace, ast.casting;

/++
  1. A tuple behaves like a struct
  2. A tuple accepts index and slice notation.
  3. There is no such thing as a size-one tuple.
  4. A tuple is matched via '()' and ','.
++/

class Tuple : Type {
  /// 1.
  Structure wrapped;
  NSCache!(IType) typecache;
  NSCache!(int) offsetcache;
  IType[] types() { return wrapped.selectMap!(RelMember, "$.type")(&typecache); }
  int[] offsets() { return wrapped.selectMap!(RelMember, "$.offset")(&offsetcache); }
  override {
    int size() { return wrapped.size; }
    string mangle() { return "tuple_"~wrapped.mangle(); }
    ubyte[] initval() { return wrapped.initval(); }
    string toString() { return Format("Tuple", (fastcast!(Structure)~ wrapped).members); }
    int opEquals(IType it) {
      if (!super.opEquals(it)) return false;
      it = resolveType(it);
      auto tup = fastcast!(Tuple) (it);
      assert(!!tup);
      // Lockstep iteration. Yummy.
      int[2] offs;
      Structure[2] sf;
      sf[0] = wrapped;
      sf[1] = tup.wrapped;
      bool[2] bailcond;
      void advance(int i) {
        do {
          if (offs[i] == sf[i].field.length) break;
        } while (!fastcast!(RelMember) (sf[i].field[offs[i]++]._1));
        bailcond[i] = offs[i] == sf[i].field.length;
      }
      
      advance(0); advance(1);
      if (bailcond[0] || bailcond[1]) return bailcond[0] == bailcond[1];
      
      Stuple!(IType, int) get(int i) {
        auto cur = fastcast!(RelMember) (sf[i].field[offs[i]++]._1);
        advance(i);
        return stuple(cur.type, cur.offset);
      }
      while (true) {
        auto elem1 = get(0), elem2 = get(1);
        if (elem1._0 != elem2._0 || elem1._1 != elem2._1)
          return false;
        if (bailcond[0] || bailcond[1]) return bailcond[0] == bailcond[1];
      }
      return true;
    }
  }
}

Object gotBraceExpr(ref string text, ParseCb cont, ParseCb rest) {
  Object obj; // exclusively for non-exprs.
  auto t2 = text;
  if (!rest(t2, "tree.expr", &obj, (Object obj) { return !fastcast!(Expr) (obj); }))
    return null;
  if (t2.accept(")")) {
    text = t2;
    return obj;
  } else {
    if (!t2.accept(","))
      t2.setError("Failed to match single-tuple");
    return null;
  }
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces", "6", "(");

Tuple mkTuple(IType[] types...) {
  auto tup = new Tuple;
  New(tup.wrapped, cast(string) null);
  tup.wrapped.packed = true;
  foreach (i, type; types)
    new RelMember(qformat("tuple_member_", i), type, tup.wrapped);
  return tup;
}

Object gotTupleType(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  IType[] types;
  if (t2.bjoin(
        !!rest(t2, "type", &ty),
        t2.accept(","),
        { types ~= ty; }
      ) &&
      t2.accept(")")
    ) {
    if (!types.length) return null; // what are you doing man.
    text = t2;
    return mkTuple(types);
  } else return null;
}
mixin DefaultParser!(gotTupleType, "type.tuple", "37", "(");

class RefTuple : MValue {
  import ast.assign;
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
      return new RefTuple(newlist);
    }
    IType valueType() { return baseTupleType; }
    void emitAsm(AsmFile af) {
      mkTupleValueExpr(getAsExprs).emitAsm(af);
    }
    string toString() {
      return Format("reftuple(", mvs, ")");
    }
    void emitAssignment(AsmFile af) {
      mixin(mustOffset("-valueType().size"));
      auto tup = fastcast!(Tuple)~ baseTupleType;
      
      auto offsets = tup.offsets();
      int data_offs;
      foreach (i, target; mvs) {
        if (offsets[i] != data_offs) {
          assert(offsets[i] > data_offs);
          af.sfree(offsets[i] - data_offs);
        }
        mixin(mustOffset("-target.valueType().size"));
        target.emitAssignment(af);
        data_offs += target.valueType().size;
      }
      if (tup.size != data_offs)
        af.sfree(tup.size - data_offs);
    }
  }
}

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
    // logln("member access to a ", rc, " - ", mae.stm);
    auto mbs = str.members();
    if (mbs.length > 1 && rt.mvs.length == 1) {
      rt = fastcast!(RefTuple) (rt.mvs[0]);
      if (rt) goto retry;
      else return null; // TODO: I don't get this. 
    }
    if (!rt || rt.mvs.length != mbs.length) {
      logln("ref tuple not large enough for this cast! ");
      logln(rt, " but ", mbs);
      asm { int 3; }
    }
    int offs = -1;
    foreach (id, entry; mbs) if (entry is mae.stm) { offs = id; break; }
    if (offs == -1) fail();
    return fastcast!(Itr) (rt.mvs[offs]);
  };
}

Expr mkTupleValueExpr(Expr[] exprs...) {
  auto tup = mkTuple(exprs /map/ (Expr ex) { return ex.valueType(); });
  return new RCE(tup, new StructLiteral(tup.wrapped, exprs.dup));
}

class LValueAsMValue : MValue {
  LValue sup;
  mixin MyThis!("sup");
  mixin defaultIterate!(sup);
  override {
    LValueAsMValue dup() { return new LValueAsMValue(sup.dup); }
    string toString() { return Format("lvtomv(", sup, ")"); }
    void emitAsm(AsmFile af) { sup.emitAsm(af); }
    IType valueType() { return sup.valueType(); }
    import ast.assign;
    void emitAssignment(AsmFile af) {
      (new Assignment(
        sup,
        new Placeholder(sup.valueType()),
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
      return forcedConvert(foldex(reinterpret_cast(newtype, ex)));
    }
    return ex;
  };
}

Expr mkTupleExpr(Expr[] exprs...) {
  bool allMValues = true;
  MValue[] arr;
  foreach (ex; exprs) {
    if (!fastcast!(MValue) (ex)) {
      auto lv = fastcast!(LValue)~ ex;
      if (!lv) {
        allMValues = false;
        break;
      }
      arr ~= new LValueAsMValue(lv);
    } else arr ~= fastcast!(MValue)~ ex;
  }
  auto vt = mkTupleValueExpr(exprs);
  if (!allMValues) return vt;
  else return new RefTuple(arr);
}

/// 4.
import ast.math: AsmFloatBinopExpr;
Object gotTupleExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr[] exprs;
  Expr ex;
  auto t2 = text;
  if (t2.accept(")")) {
    text = t2;
    // lol wat
    return fastcast!(Object)~ mkTupleExpr();
  }
  if (!t2.bjoin(
      !!rest(t2, "tree.expr", &ex),
      t2.accept(","),
      {
        exprs ~= ex;
      }
    ) || !t2.accept(")")) {
    t2.setError("Unknown identifier");
    return null;
  }
  text = t2;
  return fastcast!(Object)~ mkTupleExpr(exprs);
}
mixin DefaultParser!(gotTupleExpr, "tree.expr.tuple", "60", "(");

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
    if (!t2.accept("[")) return null;
    
    auto tup = fastcast!(Tuple) (cur);
    if (!tup)
      return null;
    
    if (!rest(t2, "tree.expr", &len)) return null;
    if (!t2.accept("]"))
      t2.failparse("Expected closing ']' for tuple index access");
    
    auto backup_len = len;
    if (!gotImplicitCast(len, (IType it) { return test(Single!(SysInt) == it); }))
      t2.failparse("Need int for tuple index access, not ", backup_len);
    opt(len);
    len = foldex(len);
    if (auto ie = fastcast!(IntExpr) (len)) {
      text = t2;
      auto types = tup.types();
      if (ie.num >= types.length)
        text.failparse(ie.num, " too large for tuple of ", types.length, "!");
      return types[ie.num];
    } else
      t2.failparse("Need foldable constant for tuple index access, not ", len);
  };
}
