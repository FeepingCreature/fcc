module ast.tuples;

import ast.base, ast.structure, ast.namespace, ast.casting, ast.opers;
import tools.functional: map, apply;

/++
  1. A tuple behaves like a struct
  2. A tuple accepts index and slice notation.
  3. There is no such thing as a size-one tuple.
  4. A tuple is matched via '()' and ','.
++/

class Tuple_ : Type, RelNamespace {
  /// 1.
  Structure wrapped;
  string[] names;
  // force to stay tuple, even if only 1 member. enables the .tuple property.
  bool forced;
  NSCache!(IType) typecache;
  NSCache!(int) offsetcache;
  this() { }
  IType[] types() { return wrapped.selectMap!(RelMember, "$.type")(&typecache); }
  override {
    bool isTempNamespace() { return false; }
    Object lookupRel(string str, Expr base, bool isDirectLookup = true) {
      if (!base) return null;
      int idx;
      if (readIndexShorthand(str, idx))
        return fastcast!(Object) (lookupOp("index"[], base, mkInt(idx)));
      if (auto res = wrapped.lookupRel(str, reinterpret_cast(wrapped, base), isDirectLookup)) return res;
      return null;
    }
    string llvmSize() { return wrapped.llvmSize(); }
    string llvmType() { return wrapped.llvmType(); }
    bool isComplete() { return wrapped.isComplete; }
    string mangle() {
      string res = "tuple_";
      wrapped.select((string, RelMember member) { res = qformat(res, "_", member.type.mangle); });
      return res;
    }
    string toString() {
      string res;
      foreach (i, ty; types()) {
        if (i) res ~= ", ";
        res ~= Format(ty);
        if (names && names[i]) res ~= Format(" ", names[i]);
      }
      if (forced) return "tuple(" ~ res ~ ")";
      return "(" ~ res ~ ")";
    }
    int opEquals(IType it) {
      if (!super.opEquals(it)) return false;
      it = resolveType(it);
      auto tup = fastcast!(Tuple) (it);
      assert(!!tup);
      if (forced != tup.forced) return false; // different behavior, different type
      auto types1 = types(), types2 = tup.types();
      if (types1.length != types2.length) return false;
      for (int i = 0; i < types1.length; ++i) {
        if (types1[i] != types2[i]) return false;
      }
      return true;
    }
  }
}

final class Tuple : Tuple_ {
  static const isFinal = true;
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
  if (globmode == !fastcast!(Expr) (obj))
    return null;
  if (globmode || t2.accept(")"[])) {
    text = t2;
    return obj;
  } else {
    if (!t2.accept(","[])) {
      if (!globmode) {
        auto t3 = text;
        IType throwaway;
        if (t3.accept("(") && rest(t3, "type", &throwaway)) {
          return null; // not supposed to be an expr tuple
        }
        t2.failparse("Expected closing paren");
      }
      t2.setError("Failed to match single-tuple"[]);
    }
    return null;
  }
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces"[], "6"[]);

Tuple[string] tupcache;

Tuple mkNewTuple(IType[] types, string[] names = null) {
  auto tup = fastalloc!(Tuple)();
  tup.wrapped = fastalloc!(Structure)(cast(string) null);
  tup.wrapped.packed = true;
  tup.names = names;
  foreach (i, type; types) {
    if (names && names[i])
      fastalloc!(RelMember)(names[i], type, tup.wrapped);
    else
      // fastalloc!(RelMember)(qformat("tuple_member_"[], i), type, tup.wrapped);
      fastalloc!(RelMember)(cast(string) null, type, tup.wrapped);
  }
  return tup;
}

Tuple mkTuple(IType[] types...) { return mkTuple(types, null); }
Tuple mkTuple(IType[] types, string[] names) {
  string hash;
  if (types.length == 1) {
    hash = types[0].mangle();
    if (names) hash ~= names[0];
    if (auto p = hash in tupcache) return *p;
  }
  foreach (type; types) if (Single!(Void) == type) {
    logln("Cannot make tuple: must not contain void, "[], types);
    fail;
  }
  auto tup = mkNewTuple(types, names);
  if (hash) tupcache[hash] = tup;
  return tup;
}

Object gotTupleType(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  IType[] types;
  string[] names;
  string ident;
  IType lastTypeAdded;
  if (t2.bjoin(
        (rest(t2, "type"[], &ty) /*|| (ty = lastTypeAdded, ty)*/) && (t2.gotIdentifier(ident) || (ident = null, true)),
        t2.accept(","[]),
        { types ~= ty; lastTypeAdded = ty; names ~= ident; }
      ) &&
      t2.accept(")"[])
    ) {
    if (!types.length) { text = t2; return mkTuple(); } // templateFoo!()
    text = t2;
    // logln("mkTuple(", types, ", ", names, ")");
    return mkTuple(types, names);
  } else return null;
}
mixin DefaultParser!(gotTupleType, "type.tuple"[], "37"[], "("[]);

import ast.assign;

final class RefTuple : MValue, IRefTuple {
  IType baseTupleType;
  MValue[] mvs;
  mixin defaultIterate!(mvs);
  mixin defaultCollapse!();
  static const isFinal = true;
  this(MValue[] mvs...) {
    this.mvs = mvs.dup;
    baseTupleType = mkTupleValueExpr(getAsExprs()).valueType();
  }
  MValue[] getMVs() { return mvs; }
  RefTuple dup() {
    auto newlist = mvs.dup;
    foreach (ref entry; newlist) entry = entry.dup;
    return fastalloc!(RefTuple)(newlist);
  }
  IType[] types() { return (fastcast!(Tuple) (baseTupleType)).types(); }
  bool forced() { return (fastcast!(Tuple) (baseTupleType)).forced; }
  Expr[] getAsExprs() {
    auto exprs = new Expr[mvs.length];
    foreach (i, mv; mvs) exprs[i] = mv;
    return exprs;
  }
  IType valueType() { return baseTupleType; }
  void emitLLVM(LLVMFile lf) {
    mkTupleValueExpr(getAsExprs).emitLLVM(lf);
  }
  string toString() {
    return Format("reftuple("[], mvs, ")"[]);
  }
  void emitAssignment(LLVMFile lf) {
    auto var = lf.pop();
    auto vartype = typeToLLVM(baseTupleType);
    foreach (i, target; mvs) {
      mixin(mustOffset("0"));
      load(lf, "extractvalue ", vartype, " ", var, ", ", i);
      auto tt = target.valueType(), tsa = typeToLLVM(tt, true), tsb = typeToLLVM(tt);
      if (tsa != tsb) {
        llcast(lf, tsa, tsb, lf.pop(), target.valueType().llvmSize());
      }
      target.emitAssignment(lf);
    }
  }
}

import ast.aggregate;
static this() {
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

Expr mkTupleValueExprBase(Expr[] exprs, bool mayDiscard) {
  auto tup = mkTuple(
    exprs /map/ (Expr ex) { return ex.valueType(); },
    exprs /map/ (Expr ex) { if (auto na = fastcast!(NamedArg)(ex)) return na.name; return cast(string) null; }
  );
  return fastalloc!(RCE)(tup, fastalloc!(StructLiteral)(tup.wrapped, exprs.dup, mayDiscard));
}

Expr mkTupleValueExpr(Expr[] exprs...) { return mkTupleValueExprBase(exprs, false); }
Expr mkTupleValueExprMayDiscard(Expr[] exprs...) { return mkTupleValueExprBase(exprs, true); }

class LValueAsMValue : MValue {
  LValue sup;
  mixin MyThis!("sup"[]);
  mixin defaultIterate!(sup);
  mixin defaultCollapse!();
  override {
    LValueAsMValue dup() { return fastalloc!(LValueAsMValue)(sup.dup); }
    string toString() { return Format("lvtomv("[], sup, ")"[]); }
    void emitLLVM(LLVMFile lf) { sup.emitLLVM(lf); }
    IType valueType() { return sup.valueType(); }
    import ast.assign;
    void emitAssignment(LLVMFile lf) {
      emitAssign(lf, sup, fastalloc!(LLVMValue)(lf.pop(), sup.valueType()));
    }
  }
}

extern(C) IType resolveTup(IType it, bool onlyIfChanged = false) {
  auto res = resolveType(it, true);
  if (auto tup = fastcast!(Tuple) (res)) {
    auto types = tup.types();
    if (!tup.forced && types.length == 1) return types[0];
  }
  if (auto rt = fastcast!(RefTuple) (res)) {
    auto types = rt.types();
    if (!rt.forced() && types.length == 1) return types[0];
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
      ex = collapse(ex);
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
        t2.failparse("expected comma when parsing tuple"[]);
      resetError;
      if (!rest(t2, "tree.expr"[], &ex))
        t2.failparse("failed to parse tuple"[]);
    } else if (exprs.length) {
      if (!t2.accept(","[])) {
        t2.setError("expected comma or closing paren");
        return null;
      }
      resetError;
      if (!rest(t2, "tree.expr"[], &ex))
        t2.failparse("failed to parse tuple");
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
      if (auto tup = fastcast!(Tuple)(ex.valueType()))
        if (tup.forced) return null;
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
    Expr index;
    if (!t2.accept("["[])) return null;
    
    auto tup = fastcast!(Tuple) (resolveTup(cur));
    if (!tup)
      return null;
    
    {
      auto backup = namespace();
      scope(exit) namespace.set(backup);
      namespace.set(new LengthOverride(backup, new IntExpr(tup.wrapped.length())));
      if (!rest(t2, "tree.expr"[], &index)) return null;
    }
    if (!t2.accept("]"[]))
      t2.failparse("Expected closing ']' for tuple index/slice access"[]);
    
    auto slice = index;
    if (gotImplicitCast(slice, (IType it) { return test(fastcast!(RangeIsh) (it)); })) {
      // see tuple_access.d:"index"
      auto rish = fastcast!(RangeIsh) (slice.valueType()),
        from = rish.getPos(slice),
        to   = rish.getEnd(slice);
      opt(from); opt(to);
      
      auto ifrom = fastcast!(IntExpr) (from), ito = fastcast!(IntExpr) (to);
      if (!ifrom || !ito) text.failparse("tuple slice argument is not constant");
      
      text = t2;
      if (ifrom.num == ito.num) return mkTuple();
      return mkTuple(tup.wrapped.slice(ifrom.num, ito.num).types);
    }
    
    auto types = tup.types();
    if (!types.length) return null; // cannot possibly mean a type-tuple tuple access
    
    auto backup_index = index;
    if (!gotImplicitCast(index, (IType it) { return test(Single!(SysInt) == it); }))
      t2.failparse("Need int for tuple index access, not "[], backup_index);
    opt(index);
    if (auto ie = fastcast!(IntExpr) (index)) {
      text = t2;
      if (ie.num >= types.length) {
        text.failparse(ie.num, " too large for tuple of "[], types.length, "!"[]);
      }
      return types[ie.num];
    } else
      t2.failparse("Need foldable constant for tuple index access, not "[], index);
  };
}
