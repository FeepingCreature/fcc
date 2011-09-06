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
    if (gotImplicitCast(ex22, (Expr ex) { return !!fastcast!(ast.iterator.Range) (fold(ex)); }))
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
    Statement init;
    auto len = iparse!(Expr, "array_length", "tree.expr")(`arr.length`, "arr", ex);
    opt(len);
    if (auto ie = fastcast!(IntExpr) (len)) {
      return iparse!(Expr, "array_iterate_int", "tree.expr.iter.for")(`[for i <- 0..len extra arr: extra[i]]`, "arr", ex, "len", ie);
    } else {
      auto lv = lvize(ex, &init);
      auto res = iparse!(Expr, "array_iterate", "tree.expr.iter.for")(`[for i <- 0..arr.length extra arr: extra[i]]`, "arr", lv);
      if (init) res = new StatementAndExpr(init, res);
      return res;
    }
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
    foldopt ~= delegate Itr(Itr it) {
      auto cie = fastcast!(CrossIndexExpr) (it);
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
      
      return fastcast!(Iterable) (mkTupleExpr(res));
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
    Cond testAdvance(LValue lv) {
      auto types = myTypes(), tup = castToTuple(lv);
      auto root = iparse!(IfStatement, "cross_iterate_init", "tree.stmt")
                         (`if (!tup[0]) { tup[0] = true; } else {}`, "tup", tup);
      foreach (i, type; types) {
        root.branch1.addStatement(iparse!(Statement, "cross_iterate_init_specific", "tree.stmt")
                                         (`{ eval tup[1+i] <- tup[1+len+i]; }`,
                                          "tup", tup, "i", mkInt(i), "len", mkInt(types.length)));
      }
      IfStatement current;
      // build if tree
      foreach_reverse (i, type; types) {
        auto myIf = iparse!(IfStatement, "cross_iterate_step", "tree.stmt")
                           (`if (tup[1+i] <- tup[1+len+i]) { } else { tup[1+len+i] = tup[1+len*2+i]; eval tup[1+i] <- tup[1+len+i]; }`,
                            "tup", tup, "i", mkInt(i), "len", mkInt(types.length));
        if (!current) {
          root.branch2.addStatement(myIf);
          current = myIf;
        } else {
          current.branch2.addStatement(myIf);
          current = myIf;
        }
      }
      auto term = iparse!(Statement, "cross_finalize", "tree.stmt")
                         (`tup[0] = false; `,
                          "tup", tup);
      current.branch2.addStatement(term); // wrap initializer around again
      assert(!!root);
      auto cond = iparse!(Cond, "cross_test_result", "cond")
                         (`tup[0]`,
                          "tup", tup);
      return new StatementAndCond(root, cond);
    }
    Expr currentValue(Expr ex) {
      auto tup = castToTuple(ex), types = myTypes();
      auto expr = iparse!(Expr, "cross_test_result", "tree.expr")
                         (`tup[1..len+1]`,
                          "tup", tup, "len", mkInt(types.length));
      return expr;
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
  auto es = mkTupleExpr(exprs);
  auto tup = mkTupleExpr([_false] ~ inits ~ exprs ~ exprs);
  auto tuptype = mkTupleExpr([_false] ~ inits ~ exprs ~ exprs).valueType(); // flattened
  
  auto cross = new Cross;
  cross.tup = fastcast!(Tuple) (tuptype);
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
  Tuple tup;
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
    return tup.types /map/ (IType it) { return (fastcast!(Iterator) (it)).elemType(); };
  }
  override {
    IType elemType() { return mkTuple(myTypes()); }
    string toString() { return Format("Zip[", size, "](", tup.types, ")"); }
    int size() { return tup.size; }
    string mangle() { return "zip_over_"~tup.mangle(); }
    ubyte[] initval() { return tup.initval(); }
    Cond testAdvance(LValue lv) {
      Cond res;
      auto types = myTypes(), tup = castToTuple(lv);
      foreach (i, type; types) {
        auto entry = fastcast!(LValue) (mkTupleIndexAccess(tup, i));
        if (!entry) asm { int 3; }
        auto cond = (fastcast!(Iterator) (entry.valueType())).testAdvance(entry);
        if (!res) res = cond;
        else res = new BooleanOp!("&&")(res, cond);
      }
      assert(!!res);
      return res;
    }
    Expr currentValue(Expr ex) {
      Expr[] exprs;
      auto types = myTypes();
      foreach (i, type; types) {
        auto entry = mkTupleIndexAccess(castToTuple(ex), i);
        exprs ~= (fastcast!(Iterator) (entry.valueType())).currentValue(entry);
      }
      return mkTupleExpr(exprs);
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
  auto tup = mkTupleExpr(exprs);
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

class Seq(T) : Type, T {
  Tuple tup; // current value, iterators, completion-bools (true when done)
  LValue castToTuple(LValue lv) {
    return iparse!(LValue, "cross_cast_to_tuple", "tree.expr")
                  ("*tup*:&lv", "lv", lv, "tup", tup);
  }
  Expr castToTuple(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex) return castToTuple(lv);
    return iparse!(Expr, "cross_cast_expr_to_tuple", "tree.expr")
                  ("tup:ex", "ex", ex, "tup", tup);
  }
  IType myType;
  override {
    IType elemType() { return myType; }
    string toString() { return Format("Seq(", tup.types, ")"); }
    int size() { return tup.size; }
    string mangle() { return "seq_over_"~tup.mangle(); }
    ubyte[] initval() { return tup.initval(); }
    Cond testAdvance(LValue lv) {
      auto len = (tup.types.length - 1) / 2;
      auto tup = castToTuple(lv);
      
      auto res_st = new Scope;
      Scope curBranch = res_st;
      for (int i = 0; i < len; ++i) {
        auto ifst = iparse!(IfStatement, "seq_step", "tree.stmt")
                           (`if tup[1+len+i] && tup[0] <- tup[1+i] { } else { tup[1+len+i] = false; }`,
                             curBranch, "tup", tup, "i", mkInt(i), "len", mkInt(len)
                           );
        curBranch.addStatement(ifst);
        curBranch = ifst.branch2; // fill the else{}
      }
      return new StatementAndCond(res_st, new ExprWrap(mkTupleIndexAccess(tup, 1+len+len-1 /* last bool, and be glad I didn't write "2*len" */)));
    }
    Expr currentValue(Expr ex) {
      return mkTupleIndexAccess(castToTuple(ex), 0);
    }
    static if (is(T: RichIterator)) {
      Expr length(Expr ex) {
        auto len = tup.types.length - 1;
        Expr res = mkInt(0);
        for (int i = 0; i < len; ++i) {
          auto term = iparse!(Expr, "seq_len", "tree.expr")
                             (`tup[i + 1]`, "tup", castToTuple(ex), "i", mkInt(i));
          auto sublen = (fastcast!(RichIterator)~ term.valueType()).length(term);
          res = lookupOp("+", res, sublen);
        }
        return res;
      }
      Expr index(Expr ex, Expr pos) {
        // TODO
        assert(false);
      }
      Expr slice(Expr ex, Expr from, Expr to) {
        assert(false); // moar meh
      }
    }
  }
}

Expr mkSeq(IType type, Expr[] exprs, bool rich) {
  Expr[] bools;
  setupStaticBoolLits();
  foreach (ex; exprs) bools ~= True;
  auto tup = mkTupleExpr(fastcast!(Expr) (new Filler(type)) ~ exprs ~ bools);
  if (rich) {
    auto seq = new Seq!(RichIterator);
    seq.myType = type;
    seq.tup = fastcast!(Tuple)~ tup.valueType();
    return new RCE(seq, tup);
  } else {
    auto seq = new Seq!(Iterator);
    seq.myType = type;
    seq.tup = fastcast!(Tuple)~ tup.valueType();
    return new RCE(seq, tup);
  }
}

Object gotIteratorSeq(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Could not match exprs for seq");
  bool rich = true;
  IType valueType;
  if (!gotImplicitCast(ex, delegate bool(Expr ex) {
    auto tup = fastcast!(Tuple)~ ex.valueType();
    if (!tup) return false;
    foreach (ex2; getTupleEntries(ex)) {
      ex2 = foldex(ex2);
      if (!gotImplicitCast(ex2, Single!(BogusIterator), isIterator))
        return false;
      if (!valueType)
        valueType = (fastcast!(Iterator) (ex2.valueType())).elemType();
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
  return fastcast!(Object) (mkSeq(valueType, list, rich));
}
mixin DefaultParser!(gotIteratorSeq, "tree.expr.iter.seq", null, "seq");

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
            eval var <- i2;
            int left = i2.length / 4;
            for 0..left {
              eval auto val <- i2; var += val;
              eval val <- i2; var += val;
              eval val <- i2; var += val;
              eval val <- i2; var += val;
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
            eval var <- i2;
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
// struct iterator or explicit iterator cast
Object gotXIterator(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    if (!t2.accept(".iterator")) return null; // Because fuck you.
    auto iter = fastcast!(Expr) (obj);
    if (!iter) return null;
    
    auto alreadyIterator = iter;
    if (gotImplicitCast(alreadyIterator, Single!(BogusIterator), (IType it) {
      return !!fastcast!(Iterator) (it);
    })) {
      text = t2;
      return fastcast!(Object) (alreadyIterator);
    }
    
    auto thingy = fastcast!(Object)~ iter.valueType();
    bool delegate(string) lookup;
    Namespace _ns; RelNamespace _rns;
    bool fun_ns(string id) { return test(_ns.lookup(id)); }
    bool fun_rns(string id) { return test(_rns.lookupRel(id, null)); }
    if (auto srn = fastcast!(SemiRelNamespace) (thingy)) thingy = fastcast!(Object) (srn.resolve());
    if (auto ns = fastcast!(Namespace)~ thingy) { _ns = ns; lookup = &fun_ns; }
    else if (auto rn = fastcast!(RelNamespace)~ thingy) { _rns = rn; lookup = &fun_rns; }
    if (!lookup || !lookup("value") || !lookup("advance")) {
      text.setError(obj, " does not form a valid iterator: value or advance missing. ");
      return null;
    }
    // logln("try ", t2.nextText(), "; ", thingy);
    auto test1 = iparse!(Expr, "si_test_step", "tree.expr")
                      (`evaluate (iter.value)`, "iter", iter);
    auto test2 = iparse!(Cond, "si_test_ivalid", "cond")
                      (`evaluate (iter.advance)`, "iter", iter);
    if (!test1 || !test2) {
      logln("test failed: ", !test1, ", ", !test2);
      asm { int 3; }
    }
    text = t2;
    auto si = new StructIterator(iter.valueType());
    auto res = fastcast!(Object)~ reinterpret_cast(si, iter);
    // logln(" => ", res);
    return res;
  };
}
mixin DefaultParser!(gotXIterator, "tree.rhs_partial.x_iter");

import ast.templ, ast.parse, ast.structure, ast.oop;
StructIterator[IType] cache;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto mns = namespace().get!(MiniNamespace);
    if (mns && !mns.id.startsWith("!safecode"))
      return null; // only allow this conversion in user code
    auto evt = ex.valueType();
    if (auto p = evt in cache) { if (!*p) return null; return reinterpret_cast(*p, ex); }
    auto st = fastcast!(Structure)~ evt;
    auto cr = fastcast!(ClassRef)~ evt;
    auto ir = fastcast!(IntfRef)~ evt;
    const string FAIL = "{ cache[evt] = null; return null; }";
    if (!st && !cr && !ir) mixin(FAIL);
    if (st && !(
      st.lookupRel("value", ex) &&
      st.lookupRel("advance", ex)))
      mixin(FAIL);
    if (cr && !(
      cr.myClass.lookupRel("value", ex) &&
      cr.myClass.lookupRel("advance", ex)))
      mixin(FAIL);
    if (ir && !(
      ir.myIntf.lookupRel("value", ex) &&
      ir.myIntf.lookupRel("advance", ex)))
      mixin(FAIL);
    auto si = new StructIterator(evt);
    Expr res = reinterpret_cast(si, ex);
    cache[evt] = si;
    return res;
  };
}
