module ast.tuple_access;

import ast.base, ast.tuples, ast.structure, ast.scopes;

Expr mkTupleIndexAccess(Expr tuple, int pos, bool intendedForSplit = false) {
  if (auto rt = fastcast!(RefTuple) (tuple)) {
    Expr res = rt.mvs[pos];
    if (auto lvtomv = fastcast!(LValueAsMValue) (res)) res = lvtomv.sup;
    return res;
  }
  auto tup = fastcast!(Tuple) (resolveType(tuple.valueType()));
  auto wrapped = tup.wrapped;
  
  MemberAccess_Expr res;
  if (fastcast!(LValue)~ tuple) res = fastalloc!(MemberAccess_LValue)();
  else res = fastalloc!(MemberAccess_Expr)();
  res.base = reinterpret_cast(wrapped, tuple);
  res.intendedForSplit = intendedForSplit;
  res.name = qformat("_"[], pos);
  
  auto temps = wrapped.selectMap!(RelMember, "$"[]);
  if (pos >= temps.length) { logln("index access length violation: "[], pos, " > "[], temps.length, " for "[], tuple); fail; }
  res.stm = temps[pos];
  
  auto types = tup.types();
  return reinterpret_cast(types[pos], res);
}

// we can safely assume here that any tmpizing measures have already been taken
// and that our base expr is already multi-access/single-access safe,
// since we get called only from getTupleEntries, which handles that stuff.
Expr tuple_access_opt(Expr ex) {
  if (auto rce = fastcast!(RCE)(ex)) {
    auto cur = ex;
    while (true) {
      if (auto rce2 = fastcast!(RCE)(cur)) cur = rce2.from;
      else break;
    }
    if (auto mae = fastcast!(MemberAccess_Expr)(cur)) {
      auto base = mae.base;
      while (true) {
        if (auto rce2 = fastcast!(RCE)(base)) base = rce2.from;
        else break;
      }
      if (auto sl = fastcast!(StructLiteral)(base)) {
        if (sl.valueType() == mae.base.valueType())
          return sl.exprs[mae.stm.index];
        // logln(" ---- ", sl.valueType());
        // logln(" ---- ", mae.base.valueType());
        // logln(sl.exprs);
        // logln(mae.stm);
      }
      // logln(">> ", (cast(Object) base).classinfo.name, " ", base);
      // asm { int 3; }
    }
  }
  // logln((cast(Object) ex).classinfo.name, " ", ex);
  // asm { int 3; }
  return ex;
}

import ast.modules;
// Note: if you use this method, you MUST make use of each returned expr,
// or else be sure that your base expression has NO side effects for partial evaluation.
// Otherwise, use mkTupleIndexAccess.
Expr[] getTupleEntries(Expr tuple, Statement* initst = null, bool dontLvize = false) {
  auto tt = fastcast!(Tuple) (resolveType(tuple.valueType()));
  if (!tt) return null;
  auto count = tt.types.length;
  if (count) {
    Expr mkcheap(Expr ex, Statement* late_init = null) {
      bool isCheap(Expr ex) { // cheap to flatten
        return _is_cheap(ex, CheapMode.Flatten);
      }
      if (dontLvize || isCheap(ex)) return ex;
      if (late_init) {
        Statement st2; Expr ex2;
        if (auto sam = fastcast!(StatementAndMValue) (ex)) {
          st2 = sam.first;
          ex2 = sam.second;
        }
        if (auto sal = fastcast!(StatementAndLValue) (ex)) {
          st2 = sal.first;
          ex2 = sal.second;
        }
        if (auto sae = fastcast!(StatementAndExpr) (ex)) {
          st2 = sae.first;
          ex2 = sae.second;
        }
        if (st2 && ex2) {
          if (isCheap(ex2)) {
            *late_init = st2;
            return tuple_access_opt(ex2);
          }
        }
      }
      if (!namespace()) {
        fail;
      }
      // force allocation
      ex = tmpize_if_possible(ex, late_init);
      return tuple_access_opt(ex);
    }
    if (!initst) {
      tuple = mkcheap(tuple);
    } else {
      Statement st;
      tuple = mkcheap(tuple, &st);
      if (st) *initst = st;
    }
  }
  Expr[] res;
  for (int i = 0; i < count; ++i)
    res ~= tuple_access_opt(mkTupleIndexAccess(tuple, i, true));
  return res;
}

import ast.parse, ast.fold, ast.int_literal, ast.namespace, ast.opers;
static this() {
  defineOp("index"[], delegate Expr(Expr e1, Expr e2) {
    Tuple tup;
    if (!gotImplicitCast(e1, Single!(HintType!(Tuple)), (IType it) {
      tup = fastcast!(Tuple) (resolveType(it));
      return tup && tup.types.length != 1; // resolve ambiguity with array index
    }))
      return null;
    int count;
    tup.wrapped.select((string, RelMember rm) { count ++; }, &tup.wrapped.rmcache);
    /// 2.1
    if (!gotImplicitCast(e2, Single!(SysInt), (IType it) { return test(Single!(SysInt) == it); }))
      return null;
    opt(e2);
    auto ie = fastcast!(IntExpr) (e2);
    if (!ie) {
      return null;
      // throw new Exception(Format(e2, " could not be simplified to an int in tuple index access"[]));
    }
    if (ie.num < 0 || ie.num !< count)
      throw new Exception(Format(ie.num, " out of bounds for tuple access"[]));
    return fastcast!(Expr) (mkTupleIndexAccess(e1, ie.num));
  });
  defineOp("length"[], delegate Expr(Expr ex) {
    Tuple tup;
    if (!gotImplicitCast(ex, (IType it) {
      tup = fastcast!(Tuple) (resolveType(it));
      return tup && tup.types.length != 1; // resolve ambiguity with array length
    }))
      return null;
    return mkInt(tup.types.length);
  });
}

import ast.casting;
static this() {
  defineOp("index"[], delegate Expr(Expr e1, Expr e2) {
    auto tup = fastcast!(Tuple) (resolveType(e1.valueType()));
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
    opt(from); opt(to);
    auto ifrom = fastcast!(IntExpr) (from), ito = fastcast!(IntExpr) (to);
    if (!ifrom || !ito) fail("fail"[]);
    
    auto start = tup.wrapped.selectMember(ifrom.num).makeOffset(tup.wrapped);
    if (ifrom.num == ito.num) {
      return mkTupleExpr();
    }
    auto restype = mkTuple(tup.wrapped.slice(ifrom.num, ito.num).types);
    auto res = iparse!(Expr, "tuple_slice"[], "tree.expr"[])
                      (`*restype*:(void*:&lv + base)`,
                       "restype"[], restype, "lv"[], fastcast!(LValue)~ e1,
                       "base"[], llvmval(start));
    return res;
  });
}

import ast.fun;
class WithSpace : Namespace {
  Object[] spaces;
  Expr pureValue;
  Expr[] values;
  this(Expr ex) {
    sup = namespace();
    spaces ~= fastcast!(Object) (ex.valueType());
    values ~= ex;
  }
  this(Object[] spaces, Expr pureValue, Expr[] values) {
    sup = namespace();
    this.spaces = spaces;
    this.pureValue = pureValue;
    this.values = values;
  }
  override {
    string mangle(string name, IType type) { assert(false); }
    Object lookup(string name, bool local = false) {
      if (name == "this") // skip the riffr(lf)f
        return get!(Function).lookup("this", local);
      if (name == "that"[]) {
        if (!pureValue) throw new Exception("Oops. "[]);
        return fastcast!(Object) (pureValue);
      }
      foreach (i, space; spaces) {
        auto rns = fastcast!(RelNamespace) (space);
        
        if (!rns) 
          if (auto srns = fastcast!(SemiRelNamespace) (space))
            rns = srns.resolve();
        
        if (auto srns = fastcast!(SemiRelNamespace) (rns))
          rns = srns.resolve();
        
        if (rns) {
          if (auto res = rns.lookupRel(name, values[i], false)) return res;
        } else if (auto ns = fastcast!(Namespace) (space)) {
          if (auto res = ns.lookup(name, local)) return res;
        }
      }
      return sup.lookup(name, local);
    }
  }
}

import ast.casting, ast.pointer, ast.vardecl, ast.conditionals;
Object gotWithTupleExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Object obj) {
    {
      auto t2 = text;
      if (!t2.accept("("[])) return null;
    }
    auto ex = fastcast!(Expr) (obj);
    WithTempExpr wte; // Careful!!
    if (ex) {
      ex = forcedConvert(ex);
      if (!_is_cheap(ex, CheapMode.Multiple)) {
        if (auto lv = fastcast!(LValue) (ex)) {
          wte = fastalloc!(WithTempExpr)(fastalloc!(RefExpr)(lv));
          ex = fastalloc!(DerefExpr)(wte.val);
        } else {
          wte = fastalloc!(WithTempExpr)(ex);
          ex = wte.val;
        }
      }
      while (fastcast!(Pointer) (resolveType(ex.valueType())))
        ex = fastalloc!(DerefExpr)(ex);
    }
    
    if (auto it = fastcast!(IType) (obj))
      obj = fastcast!(Object) (resolveType(it));
    
    Object[] spaces;
    Expr[] values;
    
    if (ex) {
      gotImplicitCast(ex, (Expr ex) {
        auto it = ex.valueType();
        if (fastcast!(Namespace) (it) || fastcast!(RelNamespace) (it) || fastcast!(SemiRelNamespace) (it)) {
          spaces ~= fastcast!(Object) (it);
          values ~= ex;
        } else cleanupex(ex, true);
        return false;
      }, false);
    } else {
      if (auto ns = fastcast!(Namespace) (obj)) {
        spaces ~= obj; values ~= null;
      } else if (auto rn = fastcast!(RelNamespace) (obj)) {
        spaces ~= obj; values ~= null;
      }
    }
    
    if (!spaces.length)
      if (ex)
        text.failparse("Not a [rel]namespace: type "[], ex.valueType());
      else
        text.failparse("Not a [rel]namespace: obj "[], obj.classinfo.name, ": "[], obj);
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(fastalloc!(WithSpace)(spaces, ex, values));
    
    Object res;
    // if (!rest(text, "tree.expr _tree.expr.bin"[], &res) && !rest(text, "cond"[], &res))
    if (!rest(text, "tree.expr.tuple"[], &res) && !rest(text, "cond"[], &res))
      text.failparse("Couldn't get with-tuple expr"[]);
    if (wte) {
      auto rex = fastcast!(Expr) (res);
      if (!rex) text.failparse("Bad: used non-expr in context where expr is sole viable option"[]);
      if (auto mv = fastcast!(MValue) (rex)) {
        // hax
        auto mvwte = fastalloc!(WithTempMValue)();
        mvwte.copy(wte);
        wte = mvwte;
      }
      wte.superthing = rex;
      return wte;
    }
    else return res;
  };
}
mixin DefaultParser!(gotWithTupleExpr, "tree.rhs_partial.withtuple"[], null, "."[]);

static this() {
  /// 3.
  implicits ~= delegate void(Expr ex, void delegate(Expr) dg) {
    while (true) {
      auto tup = fastcast!(Tuple) (resolveType(ex.valueType()));
      if (!tup) return;
      if (tup.types.length != 1) return;
      if (tup !is ex.valueType()) ex = reinterpret_cast(tup, ex);
      ex = mkTupleIndexAccess(ex, 0);
      dg(ex);
    }
  };
  // cast into tuples
  implicits ~= delegate void(Expr ex, IType it, void delegate(Expr) dg) {
    it = resolveType(it);
    if (!it || !fastcast!(Tuple) (it)) return;
    if (auto tup = fastcast!(Tuple) (resolveType(ex.valueType()))) {
      auto types = (fastcast!(Tuple) (it)).types;
      if (types.length != tup.types.length)
        return;
      Statement initst;
      auto exprs = getTupleEntries(ex, &initst);
      foreach (i, ref ex2; exprs) {
        if (!gotImplicitCast(ex2, types[i], (IType it) { return !!(it == types[i]); }))
          return;
      }
      auto t = mkTupleExpr(exprs);
      if (initst) t = mkStatementAndExpr(initst, t);
      dg(t);
    }
  };
}

static this() {
  defineOp("=="[], delegate Expr(Expr ex1, Expr ex2) {
    auto tup1 = fastcast!(Tuple) (resolveType(ex1.valueType())), tup2 = fastcast!(Tuple) (resolveType(ex2.valueType()));
    if (!tup1 || !tup2) return null;
    if (tup1 != tup2) throw new Exception(Format("Cannot compare: incompatible tuples, "[], tup1, ", "[], tup2));
    return tmpize_ref_maybe(ex1, delegate Expr(Expr ex1) {
      return tmpize_ref_maybe(ex2, delegate Expr(Expr ex2) {
        Cond res;
        auto ent1 = getTupleEntries(ex1), ent2 = getTupleEntries(ex2);
        foreach (i, se1; ent1) {
          auto se2 = ent2[i];
          auto cmp = ex2cond(lookupOp("==", se1, se2));
          if (!res) res = cmp;
          else res = fastalloc!(AndOp)(res, cmp);
        }
        return fastalloc!(CondExpr)(res);
      });
    });
  });
  // and for structs too while we're here ..
  defineOp("=="[], delegate Expr(Expr ex1, Expr ex2) {
    auto str1 = fastcast!(Structure) (resolveType(ex1.valueType())), str2 = fastcast!(Structure) (resolveType(ex2.valueType()));
    if (!str1 || !str2) return null;
    if (str1 != str2) throw new Exception(Format("cannot compare: different structs, "[], str1, ", "[], str2));
    return tmpize_ref_maybe(ex1, delegate Expr(Expr ex1) {
      return tmpize_ref_maybe(ex2, delegate Expr(Expr ex2) {
        Cond res;
        auto ml1 = str1.members(), ml2 = str2.members();
        foreach (i, m1; ml1) {
          auto m2 = ml2[i];
          auto cmp = ex2cond(lookupOp("==", fastcast!(Expr) (m1.transform(ex1)), fastcast!(Expr) (m2.transform(ex2))));
          if (!res) res = cmp;
          else res = fastalloc!(AndOp)(res, cmp);
        }
        return fastalloc!(CondExpr)(res);
      });
    });
  });
}

pragma(set_attribute, _make_tupleof, externally_visible);
extern(C) Expr _make_tupleof(Structure str, Expr ex) {
  auto ml = str.members();
  Expr[] reslist;
  foreach (member; ml) reslist ~= fastcast!(Expr) (member.transform(ex));
  return mkTupleExpr(reslist);
}
