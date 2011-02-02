module ast.iterator_ext;

import ast.base, ast.iterator;

bool delegate(IType) isRichIterator, isIterator;

import
  ast.casting, ast.int_literal, ast.opers, ast.modules,
  ast.fold, ast.namespace, ast.arrays, ast.static_arrays,
  ast.tuples, ast.tuple_access;
static this() {
  isRichIterator = delegate bool(IType it) { return !!fastcast!(RichIterator) (it); };
  isIterator = delegate bool(IType it) { return !!fastcast!(Iterator) (it); };
  defineOp("x", delegate Expr(Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex2, (Expr ex) { return !!fastcast!(IntExpr) (fold(ex)); }))
      return null;
    auto ex22 = ex2;
    if (gotImplicitCast(ex22, (Expr ex) { return !!cast(ast.iterator.Range) fold(ex); }))
      ex2 = ex22;
    auto count = (fastcast!(IntExpr)~ fold(ex2)).num;
    assert(count > 0);
    Expr[] rep;
    while (count--) rep ~= ex1.dup;
    return mkTupleExpr(rep);
  });
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (!fastcast!(Array) (ex.valueType()) && !fastcast!(StaticArray) (ex.valueType()) && !fastcast!(ExtArray) (ex.valueType())) return null;
    if (!sysmod) return null; // required
    if (!expect || !fastcast!(Iterator) (expect))
      return null;
    auto dcme = new DontCastMeExpr(ex);
    auto range = iparse!(Expr, "array_iterate_range", "tree.expr")(`0..arr.length`, "arr", dcme);
    if (auto lv = fastcast!(CValue)~ ex) {
      return iparse!(Expr, "ref_array_iterate", "tree.expr.iter.for")(`[for i <- iter extra &arr: (*extra)[i]]`, "arr", new DontCastMeCValue(lv), "iter", range);
    }
    return iparse!(Expr, "array_iterate", "tree.expr.iter.for")(`[for i <- iter extra arr: extra[i]]`, "arr", dcme, "iter", range);
  };
}

import ast.assign;
class CrossIndexExpr : Expr {
  Cross cross;
  Expr ex, idx;
  this(Cross cross, Expr ex, Expr idx) { this.cross = cross; this.ex = ex; this.idx = idx; }
  mixin defaultIterate!(ex, idx);
  override {
    typeof(this) dup() { return new typeof(this) (cross, ex.dup, idx.dup); }
    IType valueType() { return mkTuple(cross.myTypes()); }
    void emitAsm(AsmFile af) {
      auto len = cross.myTypes().length, tup = cross.castToTuple(ex);
      auto lenex = mkInt(len);
      mkVar(af, valueType(), true, (Variable var) {
        auto root = iparse!(Scope, "cross_index_init", "tree.stmt")
                          (`{ auto count = idx; }`,
                            "tup", tup, "idx", idx, af);
        auto count = fastcast!(LValue)~ root.lookup("count");
        assert(!!count);
        for (int i = len - 1; i >= 0; --i) {
          auto iex = mkInt(i);
          auto iter = mkTupleIndexAccess(tup, 1 + i + len * 2);
          auto itype = fastcast!(RichIterator)~ iter.valueType();
          assert(!!itype);
          // value = iter[count % length]
          auto len = itype.length(iter);
          root.addStatement(new Assignment(
            fastcast!(LValue)~ mkTupleIndexAccess(var, i),
            itype.index(iter,
              lookupOp("%", count, len)
            )
          ));
          // count /= orig.length
          root.addStatement(new Assignment(
            count,
            lookupOp("/", count, len)
          ));
        }
        root.emitAsm(af);
      });
    }
  }
  static this() {
    foldopt ~= delegate Expr(Expr ex) {
      auto cie = fastcast!(CrossIndexExpr) (ex);
      if (!cie) return null;
      auto ide = fastcast!(IntExpr) (foldex(cie.idx));
      if (!ide) return null;
      auto idx = ide.num;
      
      int[] lengths;
      auto iters = cie.cross.myIters(cie.ex);
      foreach (iter; iters) {
        auto ri = fastcast!(RichIterator)~ iter.valueType();
        if (!ri) return null;
        auto lex = fastcast!(IntExpr)~
          foldex(ri.length(iter));
        if (!lex) return null;
        lengths ~= lex.num;
      }
      Expr[] res;
      auto orig_idx = idx;
      foreach_reverse (i, iter; iters) {
        auto ri = fastcast!(RichIterator)~ iter.valueType();
        auto lidx = idx % lengths[i];
        res = foldex(ri.index(iter, mkInt(lidx))) ~ res;
        idx /= lengths[i];
      }
      
      return mkTupleExpr(res);
    };
  }
}

import ast.ifstmt, ast.conditionals, ast.scopes;
class Cross : Type, RichIterator {
  Tuple tup; // bool inited, then first third current values, second third running state, last third original iterators
  LValue castToTuple(LValue lv) {
    return iparse!(LValue, "cross_cast_to_tuple", "tree.expr")
                  ("*tup*:&lv", "lv", lv, "tup", tup);
  }
  Expr castToTuple(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex) return castToTuple(lv);
    return iparse!(Expr, "cross_cast_expr_to_tuple", "tree.expr")
                  ("tup:ex", "ex", ex, "tup", tup);
  }
  IType[] myTypes() {
    return tup.types[1..$][0..$/3];
  }
  Expr[] myIters(Expr ex) {
    return getTupleEntries(castToTuple(ex))
                [1 .. $][$/3..2*$/3];
  }
  override {
    IType elemType() {
      return mkTuple(myTypes());
    }
    string toString() { return Format("Cross[", size, "](", elemType, ")"); }
    int size() { return tup.size; }
    string mangle() { return "cross_over_"~tup.mangle(); }
    ubyte[] initval() { return tup.initval(); }
    Expr yieldAdvance(LValue lv) {
      auto types = myTypes(), tup = castToTuple(lv);
      auto root = iparse!(IfStatement, "cross_iterate_init", "tree.stmt")
                         (`if (!tup[0]) { tup[0] = true; } else {}`, "tup", tup);
      foreach (i, type; types) {
        root.branch1.addStatement(iparse!(Statement, "cross_iterate_init_specific", "tree.stmt")
                                         (`{ tup[1+i] = __istep tup[1+len+i]; }`,
                                          "tup", tup, "i", mkInt(i), "len", mkInt(types.length)));
      }
      IfStatement current;
      // build if tree
      foreach_reverse (i, type; types) {
        auto myIf = iparse!(IfStatement, "cross_iterate_step", "tree.stmt")
                           (`if (tup[1+i] <- tup[1+len+i]) { } else { tup[1+len+i] = tup[1+len*2+i]; tup[1+i] = __istep tup[1+len+i]; }`,
                            "tup", tup, "i", mkInt(i), "len", mkInt(types.length));
        if (!current) {
          root.branch2.addStatement(myIf);
          current = myIf;
        } else {
          current.branch2.addStatement(myIf);
          current = myIf;
        }
      }
      assert(!!root);
      auto expr = iparse!(Expr, "cross_result", "tree.expr")
                         (`tup[1..len+1]`,
                          "tup", tup, "len", mkInt(types.length));
      return new StatementAndExpr(root, expr);
    }
    Cond terminateCond(Expr ex) {
      Cond res;
      auto types = myTypes(), tup = castToTuple(ex);
      foreach (i, type; types) {
        auto entry = iparse!(Expr, "cross_subcond", "tree.expr")
                           (`tup[i + len + 1]`, "tup", tup, "i", mkInt(i), "len", mkInt(types.length));
        auto cond = (fastcast!(Iterator)~ entry.valueType()).terminateCond(entry);
        if (!res) res = cond;
        else res = new BooleanOp!("||")(res, cond);
      }
      assert(!!res);
      return res;
    }
    Expr length(Expr ex) {
      Expr res;
      auto types = myTypes(), tup = castToTuple(ex);
      int staticlength = 1;
      foreach (i, type; types) {
        auto entry = iparse!(Expr, "cross_subcond_for_len", "tree.expr")
                           (`tup[i + len*2 + 1]`, "tup", tup, "i", mkInt(i), "len", mkInt(types.length));
        auto len = (fastcast!(RichIterator)~ entry.valueType()).length(entry);
        if (staticlength != -1) {
          if (auto ie = fastcast!(IntExpr)~ foldex(len)) {
            staticlength *= ie.num;
          } else {
            staticlength = -1;
          }
        }
        if (!res) res = len;
        else res = lookupOp("*", res, len);
      }
      if (staticlength != -1)
        return mkInt(staticlength);
      assert(!!res);
      return res;
    }
    Expr index(Expr ex, Expr pos) {
      return new CrossIndexExpr(this, ex, pos);
    }
    Expr slice(Expr ex, Expr from, Expr to) { assert(false); /* meh */ }
  }
}

Expr _false;

Expr mkCross(Expr[] exprs) {
  synchronized {
    if (!_false)
    _false = iparse!(Expr, "get_false", "tree.expr")(`sys.false`);
  }
  Expr[] inits;
  foreach (ex; exprs) {
    inits ~= new Filler((fastcast!(Iterator)~ ex.valueType()).elemType());
  }
  auto tup = mkTupleExpr([_false] ~ inits ~ exprs ~ exprs);
  auto cross = new Cross;
  cross.tup = fastcast!(Tuple)~ tup.valueType();
  return new RCE(cross, tup);
}

Object gotIteratorCross(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Could not match expr for cross");
  if (!gotImplicitCast(ex, delegate bool(Expr ex) {
    auto tup = fastcast!(Tuple)~ ex.valueType();
    if (!tup) return false;
    foreach (ex2; getTupleEntries(ex)) {
      ex2 = foldex(ex2);
      // logln("got tuple entry ", ex2);
      if (!gotImplicitCast(ex2, Single!(BogusIterator), isRichIterator))
        return false;
    }
    return true;
  }))
    text.failparse("Cannot convert ", ex, " into acceptable tuple form");
  
  auto list = getTupleEntries(ex);
  foreach (ref entry; list) {// cast for rilz
    entry = foldex(entry);
    gotImplicitCast(entry, Single!(BogusIterator), isRichIterator);
  }
  return fastcast!(Object)~ mkCross(list);
}
mixin DefaultParser!(gotIteratorCross, "tree.expr.iter.cross", null, "cross");

import ast.aggregate;
class Zip(T) : Type, T {
  Tuple tup; // half iterators, half current values
  LValue castToTuple(LValue lv) {
    return iparse!(LValue, "cross_cast_to_tuple", "tree.expr")
                  ("*tup*:&lv", "lv", lv, "tup", tup);
  }
  Expr castToTuple(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex) return castToTuple(lv);
    return iparse!(Expr, "cross_cast_expr_to_tuple", "tree.expr")
                  ("tup:ex", "ex", ex, "tup", tup);
  }
  IType[] myTypes() { return tup.types[$/2 .. $]; }
  override {
    IType elemType() { return mkTuple(myTypes()); }
    string toString() { return Format("Zip[", size, "](", tup.types, ")"); }
    int size() { return tup.size; }
    string mangle() { return "zip_over_"~tup.mangle(); }
    ubyte[] initval() { return tup.initval(); }
    Expr yieldAdvance(LValue lv) {
      auto types = myTypes(), tup = castToTuple(lv);
      auto root = new AggrStatement;
      foreach (i, type; types) {
        root.stmts ~= iparse!(Statement, "zip_iterate_step", "tree.stmt")
                             (`tup[i+len] = __istep tup[i]; `,
                              "tup", tup, "i", mkInt(i), "len", mkInt(types.length));
      }
      auto expr = iparse!(Expr, "zip_result", "tree.expr")
                         (`tup[len..len*2]`,
                          "tup", tup, "len", mkInt(types.length));
      return new StatementAndExpr(root, expr);
    }
    Cond terminateCond(Expr ex) {
      Cond res;
      auto types = myTypes(), tup = castToTuple(ex);
      foreach (i, type; types) {
        auto entry = iparse!(Expr, "zip_subcond", "tree.expr")
                           (`tup[i]`, "tup", tup, "i", mkInt(i), "len", mkInt(types.length));
        auto cond = (fastcast!(Iterator)~ entry.valueType()).terminateCond(entry);
        if (!res) res = cond;
        else res = new BooleanOp!("&&")(res, cond);
      }
      assert(!!res);
      return res;
    }
    static if (is(T: RichIterator)) {
      Expr length(Expr ex) {
        // TODO: min
        auto types = myTypes();
        auto entry = iparse!(Expr, "zip_simple_len", "tree.expr")
                            (`tup[0]`, "tup", castToTuple(ex));
        return (fastcast!(RichIterator)~ entry.valueType()).length(entry);
      }
      Expr index(Expr ex, Expr pos) {
        auto types = myTypes(), tup = castToTuple(ex);
        Expr[] exprs;
        foreach (i, type; types) {
          exprs ~= iparse!(Expr, "zip_index", "tree.expr")
                          (`tup[i][pos]`,
                          "tup", tup, "i", mkInt(i),
                          "len", mkInt(types.length),
                          "pos", pos);
        }
        return mkTupleExpr(exprs);
      }
      Expr slice(Expr ex, Expr from, Expr to) {
        assert(false); // moar meh
      }
    }
  }
}

Expr mkZip(Expr[] exprs, bool rich) {
  Expr[] inits;
  foreach (ex; exprs)
    inits ~= new Filler((fastcast!(Iterator)~ ex.valueType()).elemType());
  auto tup = mkTupleExpr(exprs ~ inits);
  if (rich) {
    auto zip = new Zip!(RichIterator);
    zip.tup = fastcast!(Tuple)~ tup.valueType();
    return new RCE(zip, tup);
  } else {
    auto zip = new Zip!(Iterator);
    zip.tup = fastcast!(Tuple)~ tup.valueType();
    return new RCE(zip, tup);
  }
}

Object gotIteratorZip(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Could not match expr for zip");
  bool rich = true;
  if (!gotImplicitCast(ex, delegate bool(Expr ex) {
    auto tup = fastcast!(Tuple)~ ex.valueType();
    if (!tup) return false;
    foreach (ex2; getTupleEntries(ex)) {
      ex2 = foldex(ex2);
      if (!gotImplicitCast(ex2, Single!(BogusIterator), isIterator))
        return false;
      auto test = ex2;
      if (!gotImplicitCast(test, isRichIterator))
        rich = false;
      else
        ex2 = test;
    }
    return true;
  }))
    text.failparse("Cannot convert ", ex, " into acceptable tuple form");
  
  auto list = getTupleEntries(ex);
  foreach (ref entry; list) {// cast for rilz
    entry = foldex(entry);
    if (rich) gotImplicitCast(entry, Single!(BogusIterator), isRichIterator);
    else gotImplicitCast(entry, Single!(BogusIterator), isIterator);
  }
  return fastcast!(Object)~ mkZip(list, rich);
}
mixin DefaultParser!(gotIteratorZip, "tree.expr.iter.zip", null, "zip");

class SumExpr : Expr {
  Iterator iter;
  Expr ex;
  mixin MyThis!("iter, ex");
  mixin defaultIterate!(ex);
  SumExpr dup() { return new SumExpr(iter, ex.dup); }
  override {
    IType valueType() { return iter.elemType(); }
    void emitAsm(AsmFile af) {
      mkVar(af, iter.elemType(), true, (Variable var) {
        if (auto ri = fastcast!(RichIterator)~ iter) {
          // unroll. TODO: decide when.
          auto stmt = iparse!(Statement, "sum_1", "tree.stmt")
          (`
          {
            auto i2 = iter;
            T temp;
            var = __istep i2;
            int left = i2.length / 4;
            for 0..left {
              var += __istep i2;
              var += __istep i2;
              var += __istep i2;
              var += __istep i2;
            }
            while temp <- i2 { var += temp; }
          } `, "iter", ex, "T", iter.elemType(), "var", var, af);
          // opt(stmt);
          stmt.emitAsm(af);
        } else {
          auto stmt = iparse!(Statement, "sum_2", "tree.stmt")
          (`
          {
            auto i2 = iter;
            T temp;
            var = __istep i2;
            while temp <- i2 { var += temp; }
          }`, "iter", ex, "T", iter.elemType(), "var", var, af);
          // opt(stmt);
          stmt.emitAsm(af);
        }
      });
    }
  }
}

import ast.vardecl;
Object gotSum(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex)) {
    text.setError("Could not match expr for sum");
    return null;
  }
  IType[] tried;
  if (!gotImplicitCast(ex, Single!(BogusIterator), (IType it) { tried ~= it; return !!fastcast!(RichIterator) (it); }))
    text.failparse("Cannot convert ", ex, " to valid iterator");
  
  return new SumExpr(fastcast!(RichIterator)~ ex.valueType(), ex);
}
mixin DefaultParser!(gotSum, "tree.expr.iter.sum", null, "sum");

import ast.templ, ast.iterator;
Object gotStructIterator(ref string text, ParseCb cont, ParseCb rest) {
  if (text == ".step)" || text == ".ivalid)")
    return null; // prevent the tests below from looping. HAX.
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    auto iter = fastcast!(Expr)~ obj;
    if (!iter) return null;
    auto thingy = fastcast!(Object)~ iter.valueType();
    bool delegate(string) lookup;
    Namespace _ns; RelNamespace _rns;
    bool fun_ns(string id) { return test(_ns.lookup(id)); }
    bool fun_rns(string id) { return test(_rns.lookupRel(id, null)); }
    if (auto srn = cast(SemiRelNamespace) thingy) thingy = fastcast!(Object)~ srn.resolve();
    if (auto ns = fastcast!(Namespace)~ thingy) { _ns = ns; lookup = &fun_ns; }
    else if (auto rn = fastcast!(RelNamespace)~ thingy) { _rns = rn; lookup = &fun_rns; }
    if (!lookup || !lookup("step") || !lookup("ivalid")) return null;
    logln("try ", t2.nextText(), "; ", thingy);
    try {
      auto test1 = iparse!(Expr, "si_test_step", "tree.expr")
                        (`eval (iter.step)`, "iter", iter);
      auto test2 = iparse!(Cond, "si_test_ivalid", "cond")
                        (`eval (iter.ivalid)`, "iter", iter);
      if (!test1 || !test2) {
        // logln("test failed: ", !test1, ", ", !test2);
        return null;
      }
    } catch (Exception ex) {
      // logln("reject due to ", ex);
      return null;
    }
    text = t2;
    auto si = new StructIterator(iter.valueType());
    auto res = fastcast!(Object)~ reinterpret_cast(si, iter);
    // logln(" => ", res);
    return res;
  };
}
mixin DefaultParser!(gotStructIterator, "tree.rhs_partial.struct_iter");

import ast.templ, ast.parse, ast.structure, ast.oop;
StructIterator[IType] cache;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto mns = namespace().get!(MiniNamespace);
    if (mns && !mns.id.startsWith("!safecode"))
      return null; // only allow this conversion in user code
    auto evt = ex.valueType();
    if (auto p = evt in cache) { return reinterpret_cast(*p, ex); }
    auto st = fastcast!(Structure)~ evt;
    auto cr = fastcast!(ClassRef)~ evt;
    // auto ir = fastcast!(IntfRef)~ evt;
    IntfRef ir = null;
    if (!st && !cr && !ir)
      return null;
    if (st && !(
      st.lookupRel("step", ex) &&
      st.lookupRel("ivalid", ex)))
      return null;
    if (cr && !(
      cr.myClass.lookupRel("step", ex) &&
      cr.myClass.lookupRel("ivalid", ex)))
      return null;
    auto si = new StructIterator(evt);
    Expr res = reinterpret_cast(si, ex);
    cache[evt] = si;
    return res;
  };
}
