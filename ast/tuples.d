module ast.tuples;

import ast.base, ast.structure, ast.casting;

/++
  1. A tuple behaves like a struct
  2. A tuple accepts index and slice notation.
  2.1. Excepting tuples with a size of one.
  3. Size-one tuples autocast to their only entry.
  4. A tuple is matched via '()' and ','.
++/

class Tuple : Type {
  /// 1.
  Structure wrapped;
  IType[] types() {
    IType[] res;
    wrapped.select((string, RelMember rm) { res ~= rm.type; });
    return res;
  }
  int[] offsets() {
    int[] res;
    wrapped.select((string, RelMember rm) { res ~= rm.offset; });
    return res;
  }
  override {
    int size() { return wrapped.size; }
    string mangle() { return "tuple_"~wrapped.mangle(); }
    ubyte[] initval() { return wrapped.initval(); }
    string toString() { return Format("Tuple", (cast(Structure) wrapped).members); }
    int opEquals(IType it) {
      if (!super.opEquals(it)) return false;
      while (true) {
        if (auto tp = cast(TypeProxy) it)
          it = tp.actualType();
        else break;
      }
      auto tup = cast(Tuple) it;
      assert(tup);
      auto sf1 = wrapped.stackframe, sf2 = tup.wrapped.stackframe;
      foreach (i, entry; sf1) {
        // can't compare byte-wise! bad!
        if (entry._0 != sf2[i]._0 || entry._2 != sf2[i]._2) return false;
      }
      return true;
    }
  }
}

Object gotBraceExpr(ref string text, ParseCb cont, ParseCb rest) {
  Object obj; // exclusively for non-exprs.
  auto t2 = text;
  if (t2.accept("(") &&
      rest(t2, "tree.expr", &obj, (Object obj) { return !cast(Expr) obj; }) &&
      t2.accept(")")
    ) {
    text = t2;
    return obj;
  } else return null;
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces", "6");

Tuple mkTuple(IType[] types...) {
  auto tup = new Tuple;
  New(tup.wrapped, cast(string) null);
  foreach (type; types)
    new RelMember(null, type, tup.wrapped);
  return tup;
}

Object gotTupleType(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  IType[] types;
  if (t2.accept("(") &&
      t2.bjoin(
        !!rest(t2, "type", &ty),
        t2.accept(","),
        { types ~= ty; }
      ) &&
      t2.accept(")")
    ) {
    text = t2;
    return mkTuple(types);
  } else return null;
}
mixin DefaultParser!(gotTupleType, "type.tuple", "37");

class RefTuple : MValue {
  import ast.assign;
  IType baseTupleType;
  MValue[] mvs;
  mixin defaultIterate!(mvs);
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
      auto tup = cast(Tuple) baseTupleType;
      
      auto offsets = tup.offsets();
      int data_offs;
      foreach (i, target; mvs) {
        if (offsets[i] != data_offs) {
          assert(offsets[i] > data_offs);
          af.sfree(offsets[i] - data_offs);
        }
        target.emitAssignment(af);
        data_offs += target.valueType().size;
      }
    }
  }
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

Expr mkTupleExpr(Expr[] exprs...) {
  bool allMValues = true;
  MValue[] arr;
  foreach (ex; exprs) {
    if (!cast(MValue) ex) {
      auto lv = cast(LValue) ex;
      if (!lv) {
        allMValues = false;
        break;
      }
      arr ~= new LValueAsMValue(lv);
    } else arr ~= cast(MValue) ex;
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
  if (t2.accept("(") &&
    t2.bjoin(
      !!rest(t2, "tree.expr", &ex),
      t2.accept(","),
      {
        exprs ~= ex;
      }
    ) && t2.accept(")")) {
    text = t2;
    return cast(Object) mkTupleExpr(exprs);
  } else return null;
}
mixin DefaultParser!(gotTupleExpr, "tree.expr.tuple", "60");

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (auto rt = cast(RefTuple) ex) {
      if (rt.mvs.length == 1) {
        if (auto lvamv = cast(LValueAsMValue) rt.mvs[0])
          return lvamv.sup;
        return rt.mvs[0];
      }
    }
    return null;
  };
}
