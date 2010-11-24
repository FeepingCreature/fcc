module ast.iterator_ext;

import ast.base, ast.iterator;

bool delegate(IType) isRichIterator, isIterator;

import
  ast.casting, ast.int_literal, ast.opers, ast.modules,
  ast.fold, ast.namespace, ast.arrays, ast.static_arrays,
  ast.tuples, ast.tuple_access;
static this() {
  isRichIterator = delegate bool(IType it) { return !!cast(RichIterator) it; };
  isIterator = delegate bool(IType it) { return !!cast(Iterator) it; };
  defineOp("x", delegate Expr(Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex2, (Expr ex) { return !!cast(IntExpr) fold(ex); }))
      return null;
    auto ex22 = ex2;
    if (gotImplicitCast(ex22, (Expr ex) { return !!cast(ast.iterator.Range) fold(ex); }))
      ex2 = ex22;
    auto count = (cast(IntExpr) fold(ex2)).num;
    assert(count > 0);
    Expr[] rep;
    while (count--) rep ~= ex1.dup;
    return mkTupleExpr(rep);
  });
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (!cast(Array) ex.valueType() && !cast(StaticArray) ex.valueType() && !cast(ExtArray) ex.valueType()) return null;
    if (!sysmod) return null; // required
    if (!expect || !cast(Iterator) expect)
      return null;
    auto dcme = new DontCastMeExpr(ex);
    auto range = iparse!(Expr, "array_iterate_range", "tree.expr")(`0..arr.length`, "arr", dcme);
    if (auto lv = cast(CValue) ex) {
      return iparse!(Expr, "ref_array_iterate", "tree.expr.iter.for")(`[for i <- iter extra &arr: (*extra)[i]]`, "arr", new DontCastMeCValue(lv), "iter", range);
    }
    return iparse!(Expr, "array_iterate", "tree.expr.iter.for")(`[for i <- iter extra arr: extra[i]]`, "arr", dcme, "iter", range);
  };
}

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
      auto lenex = new IntExpr(len);
      auto root = iparse!(Scope, "cross_index_init", "tree.stmt")
                         (`{ auto count = idx; }`,
                          "tup", tup, "idx", idx, af);
      auto count = root.lookup("count");
      assert(!!count);
      for (int i = len - 1; i >= 0; --i) {
        auto iex = new IntExpr(i);
        root.addStatement(iparse!(Statement, "cross_index_subset", "tree.semicol_stmt.assign")
                                 (`tup[1+i+len] = tup[1+i+len*2]`,
                                  "tup", tup, "i", iex, "len", lenex));
        // root.addStatement(iparse!(Statement, "cross_index_subset", "tree.stmt")
        //                          (`printf("%i: tup[%i+1] = tup[1+i+len][%i %% %i = %i] = %i\n", idx, i, count, tup[1+i+len*2].length, count % tup[1+i+len*2].length, tup[1+i+len][count % tup[1+i+len*2].length]); `,
        //                           "tup", tup, "i", iex, "len", lenex, "count", count, "idx", idx));
        root.addStatement(iparse!(Statement, "cross_index_subset", "tree.stmt")
                                 (`tup[1+i] = tup[1+i+len][count % tup[1+i+len*2].length]; `,
                                  "tup", tup, "i", iex, "len", lenex, "count", count));
        root.addStatement(iparse!(Statement, "cross_index_subset", "tree.stmt")
                                 (`count = count / tup[1+i+len*2].length; `,
                                  "tup", tup, "i", iex, "len", lenex, "count", count));
      }
      root.emitAsm(af);
      // tuple result
      iparse!(Expr, "cross_result", "tree.expr")
             (`tup[1..len+1]`,
              "tup", tup, "len", lenex).emitAsm(af);
    }
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
    if (auto lv = cast(LValue) ex) return castToTuple(lv);
    return iparse!(Expr, "cross_cast_expr_to_tuple", "tree.expr")
                  ("tup:ex", "ex", ex, "tup", tup);
  }
  IType[] myTypes() {
    return tup.types[1 .. ($-1)/3 + 1];
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
                                          "tup", tup, "i", new IntExpr(i), "len", new IntExpr(types.length)));
      }
      IfStatement current;
      // build if tree
      foreach_reverse (i, type; types) {
        auto myIf = iparse!(IfStatement, "cross_iterate_step", "tree.stmt")
                           (`if (tup[1+i] <- tup[1+len+i]) { } else { tup[1+len+i] = tup[1+len*2+i]; tup[1+i] = __istep tup[1+len+i]; }`,
                            "tup", tup, "i", new IntExpr(i), "len", new IntExpr(types.length));
        if (!current) {
          root.branch2.addStatement(myIf);
          current = myIf;
        } else {
          current.branch2.addStatement(myIf);
          current = myIf;
        }
      }
      assert(root);
      auto expr = iparse!(Expr, "cross_result", "tree.expr")
                         (`tup[1..len+1]`,
                          "tup", tup, "len", new IntExpr(types.length));
      return new StatementAndExpr(root, expr);
    }
    Cond terminateCond(Expr ex) {
      Cond res;
      auto types = myTypes(), tup = castToTuple(ex);
      foreach (i, type; types) {
        auto entry = iparse!(Expr, "cross_subcond", "tree.expr")
                           (`tup[i + len + 1]`, "tup", tup, "i", new IntExpr(i), "len", new IntExpr(types.length));
        auto cond = (cast(Iterator) entry.valueType()).terminateCond(entry);
        if (!res) res = cond;
        else res = new BooleanOp!("||")(res, cond);
      }
      assert(res);
      return res;
    }
    Expr length(Expr ex) {
      Expr res;
      auto types = myTypes(), tup = castToTuple(ex);
      foreach (i, type; types) {
        auto entry = iparse!(Expr, "cross_subcond_for_len", "tree.expr")
                           (`tup[i + len*2 + 1]`, "tup", tup, "i", new IntExpr(i), "len", new IntExpr(types.length));
        auto len = (cast(RichIterator) entry.valueType()).length(entry);
        if (!res) res = len;
        else res = lookupOp("*", res, len);
      }
      assert(res);
      return res;
    }
    Expr index(LValue lv, Expr pos) {
      return new CrossIndexExpr(this, lv, pos);
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
    inits ~= new Filler((cast(Iterator) ex.valueType()).elemType());
  }
  auto tup = mkTupleExpr([_false] ~ inits ~ exprs ~ exprs);
  auto cross = new Cross;
  cross.tup = cast(Tuple) tup.valueType();
  return new RCE(cross, tup);
}

Object gotIteratorCross(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Could not match expr for cross");
  if (!gotImplicitCast(ex, delegate bool(Expr ex) {
    auto tup = cast(Tuple) ex.valueType();
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
  return cast(Object) mkCross(list);
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
    if (auto lv = cast(LValue) ex) return castToTuple(lv);
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
                              "tup", tup, "i", new IntExpr(i), "len", new IntExpr(types.length));
      }
      auto expr = iparse!(Expr, "zip_result", "tree.expr")
                         (`tup[len..len*2]`,
                          "tup", tup, "len", new IntExpr(types.length));
      return new StatementAndExpr(root, expr);
    }
    Cond terminateCond(Expr ex) {
      Cond res;
      auto types = myTypes(), tup = castToTuple(ex);
      foreach (i, type; types) {
        auto entry = iparse!(Expr, "zip_subcond", "tree.expr")
                           (`tup[i]`, "tup", tup, "i", new IntExpr(i), "len", new IntExpr(types.length));
        auto cond = (cast(Iterator) entry.valueType()).terminateCond(entry);
        if (!res) res = cond;
        else res = new BooleanOp!("&&")(res, cond);
      }
      assert(res);
      return res;
    }
    static if (is(T: RichIterator)) {
      Expr length(Expr ex) {
        // TODO: min
        auto types = myTypes();
        auto entry = iparse!(Expr, "zip_simple_len", "tree.expr")
                            (`tup[0]`, "tup", castToTuple(ex));
        return (cast(RichIterator) entry.valueType()).length(entry);
      }
      Expr index(LValue lv, Expr pos) {
        auto types = myTypes(), tup = castToTuple(lv);
        Expr[] exprs;
        foreach (i, type; types) {
          exprs ~= iparse!(Expr, "zip_index", "tree.expr")
                          (`tup[i][pos]`,
                          "tup", tup, "i", new IntExpr(i),
                          "len", new IntExpr(types.length),
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
    inits ~= new Filler((cast(Iterator) ex.valueType()).elemType());
  auto tup = mkTupleExpr(exprs ~ inits);
  if (rich) {
    auto zip = new Zip!(RichIterator);
    zip.tup = cast(Tuple) tup.valueType();
    return new RCE(zip, tup);
  } else {
    auto zip = new Zip!(Iterator);
    zip.tup = cast(Tuple) tup.valueType();
    return new RCE(zip, tup);
  }
}

Object gotIteratorZip(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Could not match expr for zip");
  bool rich = true;
  if (!gotImplicitCast(ex, delegate bool(Expr ex) {
    auto tup = cast(Tuple) ex.valueType();
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
  return cast(Object) mkZip(list, rich);
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
        iparse!(Statement, "sum", "tree.stmt")
              (`{ bool inited; auto i2 = iter; while T temp <- i2 { if !inited { inited = true; var = temp; } else { var = var + temp; } } }`,
                "iter", ex, "T", iter.elemType(), "var", var, af).emitAsm(af);
      });
    }
  }
}

import ast.vardecl;
Object gotSum(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Could not match expr for cross");
  IType[] tried;
  if (!gotImplicitCast(ex, Single!(BogusIterator), (IType it) { tried ~= it; return !!cast(RichIterator) it; }))
    text.failparse("Cannot convert ", ex, " to valid iterator");
  
  return new SumExpr(cast(RichIterator) ex.valueType(), ex);
}
mixin DefaultParser!(gotSum, "tree.expr.iter.sum", null, "sum");

import ast.templ, ast.iterator;
Object gotStructIterator(ref string text, ParseCb cont, ParseCb rest) {
  if (text == ".step)" || text == ".ivalid)")
    return null; // prevent the tests below from looping. HAX.
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    auto iter = cast(Expr) obj;
    if (!iter) return null;
    auto thingy = cast(Object) iter.valueType();
    bool delegate(string) lookup;
    if (auto srn = cast(SemiRelNamespace) thingy) thingy = cast(Object) srn.resolve();
    if (auto ns = cast(Namespace) thingy) lookup = ns /apply/ (Namespace ns, string id) { return test(ns.lookup(id)); };
    else if (auto rn = cast(RelNamespace) thingy) lookup = rn /apply/ (RelNamespace rn, string id) { return test(rn.lookupRel(id, null)); };
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
    auto res = cast(Object) reinterpret_cast(si, iter);
    // logln(" => ", res);
    return res;
  };
}
mixin DefaultParser!(gotStructIterator, "tree.rhs_partial.struct_iter");

import ast.templ, ast.parse, ast.structure, ast.oop;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto mns = namespace().get!(MiniNamespace);
    if (mns && !mns.id.startsWith("!safecode"))
      return null; // only allow this conversion in user code
    auto st = cast(Structure) ex.valueType();
    auto cr = cast(ClassRef) ex.valueType();
    // auto ir = cast(IntfRef) ex.valueType();
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
    auto si = new StructIterator(ex.valueType());
    Expr res = reinterpret_cast(si, ex);
    // logln(" => ", res);
    return res;
  };
}
