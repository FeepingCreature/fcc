module ast.iterator;

import
  ast.base, ast.parse, ast.types, ast.namespace, ast.structure,
  ast.casting, ast.pointer, ast.tuples, ast.tuple_access,
  ast.literal_string, ast.variable, ast.assign, ast.literals,
  ast.int_literal, ast.fold, ast.conditionals, ast.literal_string,
  ast.scopes, ast.static_arrays, ast.aggregate, ast.vardecl,
  ast.aliasing, ast.opers, ast.arrays, ast.modules;

import tools.base: between;

class Range : Type, RichIterator, RangeIsh {
  IType wrapper;
  LValue castToWrapper(LValue lv) {
    return iparse!(LValue, "range_cast_to_wrapper", "tree.expr", dontopt)
                  ("*wrapper*:&lv"[], "lv"[], lv, "wrapper"[], wrapper);
  }
  Expr castExprToWrapper(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex)
      return castToWrapper(lv);
    return reinterpret_cast(wrapper, ex);
  }
  override {
    IType elemType() { return mkMemberAccess(new ast.base.Placeholder(wrapper), "cur"[]).valueType(); }
    string toString() { return Format("RangeIter["[], llvmSize, "](", wrapper, ")"); }
    string llvmSize() { return wrapper.llvmSize(); }
    string llvmType() { return wrapper.llvmType(); }
    string mangle() { return "range_over_"~wrapper.mangle(); }
    Expr currentValue(Expr ex) {
      return mkMemberAccess(castExprToWrapper(ex), "cur"[]);
    }
    Cond testAdvance(LValue lv) {
      return iparse!(Cond, "test_advance_range"[], "cond"[])
                    ("++lv.cur < lv.end"[], "lv"[], castToWrapper(lv));
    }
    Expr length(Expr ex) {
      return iparse!(Expr, "length_range"[], "tree.expr"[])
                    ("int:(ex.end - ex.cur - 1)"[], "ex"[], castExprToWrapper(ex));
    }
    Expr index(Expr ex, Expr pos) {
      return iparse!(Expr, "index_range"[], "tree.expr"[])
                    ("ex.cur + pos + 1"[],
                     "ex"[], castExprToWrapper(ex),
                     "pos"[], pos);
    }
    Expr slice(Expr ex, Expr from, Expr to) {
      return iparse!(Expr, "slice_range"[], "tree.expr"[])
                    ("(ex.cur + from) .. (ex.cur + to)"[],
                     "ex"[], castExprToWrapper(ex),
                     "from"[], from, "to"[], to);
    }
    // DOES NOT HONOR ITERATOR SEMANTICS!!
    Expr getPos(Expr ex) {
      return lookupOp("+"[], mkInt(1), mkMemberAccess(castExprToWrapper(ex), "cur"[]));
    }
    Expr getEnd(Expr ex) {
      return mkMemberAccess(castExprToWrapper(ex), "end"[]);
    }
  }
}

class ConstIntRange : Type, RichIterator, RangeIsh {
  int from, to;
  this(int f, int t) { this.from = f; this.to = t; }
  override {
    IType elemType() { return Single!(SysInt); }
    string toString() { return Format("ConstIntRange["[], llvmSize, "]()"[]); }
    string llvmSize() { return "4"; }
    string llvmType() { return "i32"; }
    string mangle() { return Format("constint_range_"[], from, "_to_"[], to).replace("-"[], "_minus_"[]); }
    Expr currentValue(Expr ex) {
      return reinterpret_cast(Single!(SysInt), ex);
    }
    import ast.conditionals: Compare;
    Cond testAdvance(LValue lv) {
      return iparse!(Cond, "test_advance_int_range"[], "cond"[])
                    ("++lv < to"[],
                     "lv"[], reinterpret_cast(Single!(SysInt), lv),
                     "to"[], mkInt(to)
                    );
    }
    Expr length(Expr ex) {
      return iparse!(Expr, "const_int_length"[], "tree.expr"[])
                    (`to - ex - 1`,
                     "ex"[], reinterpret_cast(Single!(SysInt), ex),
                     "to"[], fastalloc!(IntExpr)(to));
    }
    Expr index(Expr ex, Expr pos) {
      return iparse!(Expr, "const_index_range"[], "tree.expr"[])
                    ("ex + 1 + pos"[],
                     "ex"[], reinterpret_cast(Single!(SysInt), ex),
                     "pos"[], pos);
    }
    Expr slice(Expr ex, Expr from, Expr to) {
      opt(from); opt(to);
      auto ifrom = fastcast!(IntExpr) (from), ito = fastcast!(IntExpr) (to);
      if (ifrom && ito) {
        auto res = new ConstIntRange(this.from+ifrom.num, this.to+ito.num);
        return reinterpret_cast(res, lookupOp("+",
          lookupOp("-",
            reinterpret_cast(Single!(SysInt), ex),
            mkInt(this.from)
          ),
          ifrom
        ));
      }
      return iparse!(Expr, "slice_range"[], "tree.expr"[])
                    ("(ex + from) .. (ex + to)"[],
                     "ex"[], reinterpret_cast(Single!(SysInt), ex),
                     "from"[], from, "to"[], to);
    }
    // behaves differently from the iterator interface!!
    Expr getPos(Expr ex) {
      return lookupOp("+"[], mkInt(1), reinterpret_cast(Single!(SysInt), ex));
    }
    Expr getEnd(Expr ex) { return mkInt(to); }
  }
}

Expr mkRange(Expr from, Expr to) {
  auto wrapped = fastalloc!(Structure)(cast(string) null);
  // cur must start one early
  auto fvt = from.valueType();
  from = lookupOp("-"[], from, mkInt(1));
  if (!gotImplicitCast(from, Single!(SysInt), (IType it) { return !!(Single!(SysInt) == it); })
   && !gotImplicitCast(from, fvt, (IType it) { return !!(it == fvt); })
   && !(from = tryConvert(from, fvt), from))
    throw new Exception(Format("mkRange: "[], fvt, " does not cleanly implement integer subtraction or allow down-conversion. "[]));
  fastalloc!(RelMember)("cur"[], from.valueType(), wrapped);
  fastalloc!(RelMember)("end"[], to.valueType(), wrapped);
  auto range = new Range;
  range.wrapper = wrapped;
  return reinterpret_cast(range, fastalloc!(StructLiteral)(wrapped, [from, to]));
}

Object gotRangeIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr from, to;
  auto t2 = text;
  if (!cont(t2, &from)) return null;
  if (!t2.accept(".."[])) return null;
  if (!rest(t2, "tree.expr ,tree.expr.bin", &to))
    t2.failparse("Unable to acquire second ha(lf) of range def"[]);
  text = t2;
  bool notATuple(IType it) { return !fastcast!(Tuple) (it); }
  bool isByte(IType it) { return !!fastcast!(Byte) (it); }
  gotImplicitCast(from, &notATuple);
  gotImplicitCast(to  , &notATuple);
  from = collapse(from);
  to = collapse(to);
  if (auto sl = fastcast!(StringExpr) (from)) if (sl.str.length == 1) gotImplicitCast(from, &isByte);
  if (auto sl = fastcast!(StringExpr) (to))   if (sl.str.length == 1) gotImplicitCast(to,   &isByte);
  auto ifrom = fastcast!(IntExpr) (from), ito = fastcast!(IntExpr) (to);
  if (ifrom && ito)
    return fastcast!(Object)~ reinterpret_cast(fastalloc!(ConstIntRange)(ifrom.num, ito.num), mkInt(ifrom.num - 1));
  return fastcast!(Object)~ mkRange(from, to);
}
mixin DefaultParser!(gotRangeIter, "tree.expr.iter_range"[], "11"[]);

class StructIterator : Type, Iterator {
  IType wrapped;
  IType _elemType;
  this(IType it) {
    wrapped = it;
    scope(failure) fail;
    scope(failure) logln("it was "[], it);
    _elemType = iparse!(Expr, "si_elemtype"[], "tree.expr.eval"[])
                       (`evaluate (bogus.value)`,
                        "bogus"[], fastalloc!(PlaceholderTokenLV)(wrapped, "wrapped"[])
                       ).valueType();
  }
  override {
    string llvmSize() { return wrapped.llvmSize(); }
    string llvmType() { return wrapped.llvmType(); }
    string mangle() { return "struct_iterator_"~wrapped.mangle(); }
    IType elemType() { return _elemType; }
    Expr currentValue(Expr ex) {
      ex = reinterpret_cast(wrapped, ex);
      return iparse!(Expr, "si_value"[], "tree.expr"[])
                    (`evaluate (ex.value)`,
                     "ex"[], ex);
    }
    Cond testAdvance(LValue lv) {
      lv = fastcast!(LValue) (reinterpret_cast(wrapped, lv));
      return iparse!(Cond, "si_ivalid"[], "cond"[])
                    (`evaluate (lv.advance)`,
                     "lv"[], lv);
    }
    string toString() { return Format("si "[], wrapped); }
  }
}

static this() {
  // this was commented out to work around a really bad bug
  // if you find what the bug is: DOCUMENT IT HERE. Don't just silently comment it out!
  implicits ~= delegate Expr(Expr ex) {
    if (auto si = fastcast!(StructIterator) (ex.valueType())) {
      return reinterpret_cast(si.wrapped, ex);
    }
    return null;
  };
}

import tools.base: This, This_fn, rmSpace, PTuple, Stuple, ptuple, stuple;

interface IArrayIterator {
  Expr castToArray(Expr ex);
}

class ForIter(I) : Type, I {
  override int opEquals(IType it) {
    auto fi = fastcast!(ForIter) (it);
    if (!fi) return false;
    // return this is it; // I wish.
    return var is fi.var && extra is fi.extra;
  }
  IType wrapper;
  I itertype;
  Expr ex;
  PlaceholderToken var, extra;
  bool autofree;
  ForIter dup() {
    auto res = new ForIter;
    res.wrapper = wrapper;
    res.itertype = itertype;
    res.ex = ex.dup;
    res.var = var; res.extra = extra;
    res.autofree = autofree;
    return res;
  }
  LValue castToWrapper(LValue lv) {
    return fastalloc!(DerefExpr)(reinterpret_cast(fastalloc!(Pointer)(wrapper), fastalloc!(RefExpr)(lv)));
  }
  Expr castToWrapper(Expr ex) {
    if (auto lv = fastcast!(LValue) (ex)) return castToWrapper(lv);
    return reinterpret_cast(wrapper, ex);
  }
  LValue subexpr(LValue lv) {
    return iparse!(LValue, "foriter_get_subexpr_lv", "tree.expr", dontopt)
                  ("lv.subiter"[], "lv"[], lv);
  }
  Expr subexpr(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex) return subexpr(lv);
    opt(ex);
    // optimize subexpr of literal
    auto res = iparse!(Expr, "foriter_get_subexpr"[], "tree.expr"[])
                      ("ex.subiter"[], "ex"[], ex);
    opt(res);
    return res;
  }
  Expr[] todocache;
  Expr update(Expr ex, PlaceholderToken var, Expr newvar) {
    auto todo = todocache;
    int size;
    void add(Expr ex) {
      if (!todo) todo = new Expr[16];
      if (size == todo.length) todo.length = todo.length * 2;
      todo[size++] = ex;
    }
    Expr take() {
      return todo[--size];
    }
    scope(exit) todocache = todo;
    Expr resolveRC(Expr ex) {
      while (true) {
        if (auto rc = fastcast!(RC) (ex))
          ex = rc.from;
        else break;
      }
      return ex;
    }
    void subst(ref Iterable it) {
      if (cast(PlaceholderToken) it is var) {
        it = fastcast!(Iterable)~ newvar;
      } else {
        auto ex = fastcast!(Expr)~ it;
        if (ex) {
          if (auto fi = fastcast!(ForIter!(RichIterator)) (ex.valueType())) {
            ex = resolveRC(ex);
            auto fi2 = fi.dup;
            add(fi2.ex);
            ex.iterate(&subst);
            it = fastcast!(Iterable)~ reinterpret_cast(fi2, ex);
            return;
          } else if (auto fi = fastcast!(ForIter!(Iterator)) (ex.valueType())) {
            ex = resolveRC(ex);
            auto fi2 = fi.dup;
            add(fi2.ex);
            ex.iterate(&subst);
            it = fastcast!(Iterable)~ reinterpret_cast(fi2, ex);
            return;
          }
        }
        it.iterate(&subst);
      }
    }
    auto sex = ex.dup;
    add(sex);
    bool[Expr] done;
    while (size) {
      auto cur_ex = take();
      if (cur_ex in done) {
        logln("wtf?! didn't I do "[], cur_ex, " already?"[]);
        fail;
      }
      done[cur_ex] = true;
      cur_ex.iterate(&subst);
    }
    // optimization won't reach into types
    // cf. http://www.smbc-comics.com/index.php?db=comics&id=1927
    opt(sex); // Yes we have fully optimized sex.
    return sex;
  }
  Expr update(Expr ex, Expr iex) {
    auto var = iparse!(Expr, "foriter_ex_var_lookup"[], "tree.expr"[])
                      ("iex.var"[], "iex"[], iex);
    ex = update(ex, this.var, var);
    if (this.extra) {
      auto extra = iparse!(Expr, "foriter_ex_extra_lookup"[], "tree.expr"[])
                      ("iex.extra"[], "iex"[], iex);
      ex = update(ex, this.extra, extra);
    }
    return ex;
  }
  Statement mkForIterAssign(LValue lv, ref LValue wlv) {
    wlv = castToWrapper(lv);
    auto var = iparse!(LValue, "foriter_wlv_var", "tree.expr", dontopt)
                      ("wlv.var"[], "wlv"[], wlv);
    return fastalloc!(Assignment)(var, itertype.currentValue(subexpr(wlv.dup)));
  }
  override {
    string toString() {
      auto sizeinfo = Format(llvmSize(), ":"[]);
      (fastcast!(Structure)~ wrapper).select((string, RelMember rm) { sizeinfo ~= Format(" "[], rm.type.llvmSize()); });
      return Format("ForIter["[], sizeinfo, "]("[], itertype, ": "[], ex.valueType(), "[]) var "[], cast(void*) var, " extra "[], cast(void*) extra);
    }
    IType elemType() { return ex.valueType(); }
    string llvmSize() { return wrapper.llvmSize(); }
    string llvmType() { return wrapper.llvmType(); }
    string mangle() { return Format("for_range_over_"[], wrapper.mangle(), "_var_"[], cast(size_t) var, "_extra_"[], cast(size_t) extra); }
    Cond testAdvance(LValue lv) {
      auto res = itertype.testAdvance(subexpr(castToWrapper(lv).dup));
      if (autofree) {
        logln("btw 1 ex is type "[], subexpr(castToWrapper(lv)).valueType());
        auto ai = fastcast!(IArrayIterator) (subexpr(castToWrapper(lv)).valueType());
        auto sub = ai.castToArray(subexpr(castToWrapper(lv)));
        // logln("auto-free() of type "[], iparse!(Expr, "mew"[], "tree.expr"[])(`ex.extra`, "ex"[], sub).valueType());
        Statement freest = iparse!(Statement, "autofree_exec"[], "tree.stmt"[])
                                  (`ex.free();`, "ex"[], sub);
        res = fastalloc!(OrOp)(res, fastalloc!(StatementAndCond)(freest, cFalse));
      }
      return res;
    }
    Expr currentValue(Expr ex) {
      auto lv = fastcast!(LValue) (ex);
      if (!lv) {
        logln("TODO: mandate lvalue for curval"[]);
        fail;
      }
      LValue wlv;
      auto stmt = mkForIterAssign(lv, wlv);
      Expr exonly(Expr ex) {
        auto vt = ex.valueType();
        return new RCE(vt, ex, true);
      }
      return fastalloc!(StatementAndExpr)(stmt, exonly(update(this.ex.dup, wlv)));
    }
    static if (is(I: RichIterator)) {
      Expr length(Expr ex) {
        return itertype.length(subexpr(castToWrapper(ex).dup));
      }
      Expr index(Expr ex, Expr pos) {
        auto we = castToWrapper(ex);
        auto st = fastalloc!(Structure)(cast(string) null);
        fastalloc!(RelMember)("var"[], var.valueType(), st);
        Expr tup;
        if (extra) {
          fastalloc!(RelMember)("extra"[], extra.valueType(), st);
          tup = mkTupleExpr(
            itertype.index(subexpr(we.dup), pos),
            mkMemberAccess(we, "extra"[])
          );
        } else {
          tup = mkTupleExpr(
            itertype.index(subexpr(we.dup), pos)
          );
        }
        auto casted = reinterpret_cast(st, tup);
        return update(this.ex, casted);
      }
      Expr slice(Expr ex, Expr from, Expr to) {
        auto wr = castToWrapper(ex);
        auto st = fastcast!(Structure) (wrapper);
        auto slice = fastcast!(Expr) (itertype.slice(subexpr(wr.dup), from, to));
        if (slice.valueType().llvmType() != st.selectMap!(RelMember, "$.type.llvmType()")()[0]) {
          logln("Weird thing: slice type ", slice.valueType(), " differs from native slice ", st.selectMap!(RelMember, "$.type")()[0]);
          logln("you probably tried to slice a 'for' range over a const-int subrange with args that aren't const ints. ");
          logln("for compiler-internal reasons this cannot be supported. we apologize for the inconvenience. ");
          fail;
        }
        Expr[] field = [slice, fastalloc!(Filler)(itertype.elemType())];
        if (extra) field ~= extra;
        return reinterpret_cast(this,
          fastalloc!(StructLiteral)(st, field));
      }
    }
  }
}

class ScopeAndExpr : Expr {
  Scope sc;
  Expr ex;
  this(Scope sc, Expr ex) { this.sc = sc; this.ex = ex; }
  mixin defaultIterate!(sc, ex);
  Expr collapse() { return this; } // no check
  override {
    string toString() { return Format("sae("[], sc._body, ", "[], ex, ")"[]); }
    ScopeAndExpr dup() { return fastalloc!(ScopeAndExpr)(sc.dup, ex.dup); }
    IType valueType() { return ex.valueType(); }
    void emitLLVM(LLVMFile lf) {
      sc.id = getuid();
      mixin(mustOffset("1"));
      // logln("ex = ", ex);
      if (Single!(Void) == ex.valueType()) {
        // fixUpVariables(lf.currentStackDepth);
        auto dg = sc.open(lf)();
        ex.emitLLVM(lf);
        dg(false);
        push(lf, "poison");
      } else {
        auto var = fastalloc!(LLVMRef)(ex.valueType());
        var.allocate(lf);
        scope(success) {
          var.emitLLVM(lf);
          var.end(lf);
        }
        // fixUpVariables(lf.currentStackDepth);
        auto dg = sc.open(lf)();
        var.begin(lf);
        emitAssign(lf, var, ex);
        dg(false);
      }
    }
  }
  static this() {
    debug foldopt ~= delegate Itr(Itr it) {
      auto sae = fastcast!(ScopeAndExpr) (it);
      if (!sae) return null;
      if (!sae.sc) return null;
      auto stmt = sae.sc._body;
      assert(!stmt); // must be no statements in SAE
      return null;
    };
    foldopt ~= delegate Itr(Itr it) {
      auto sae = fastcast!(ScopeAndExpr) (it);
      if (!sae) return null;
      bool visible(Itr it2) {
        if (sae.ex is it2) return true;
        bool res;
        void check(ref Itr it) {
          if (it is it2) { res = true; return; }
          it.iterate(&check);
        }
        sae.ex.iterate(&check);
        return res;
      }
      bool allUnused = true;
      foreach (entry; sae.sc.field) {
        if (auto it = fastcast!(Itr) (entry._1)) {
          if (visible(it)) { allUnused = false; break; }
        }
      }
      with (sae.sc) {
        if (!_body && !guards && allUnused)
          return fastcast!(Iterable) (sae.ex);
      }
      return null;
    };
  }
}

Object gotForIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr sub, main;
  auto t2 = text;
  
  bool autofree;
  if (t2.accept("auto"[]) && t2.accept("~"[])) autofree = true;
  
  if (!t2.accept("for"[])) return null;
  
  string ivarname;
  auto t3 = t2;
  if (t3.gotIdentifier(ivarname) && t3.acceptLeftArrow()) {
    t2 = t3;
  } else ivarname = null;
  if (!rest(t2, "tree.expr"[], &sub))
    t2.failparse("Cannot find sub-iterator"[]);
  auto subx = sub;
  IType[] tried;
  if (!gotImplicitCast(sub, Single!(HintType!(Iterator)), (IType it) { tried ~= it; return !!fastcast!(Iterator) (it); }, false)) {
    string failtext = "Invalid sub-iterator: none of these are iterators: ";
    foreach (i, t; tried) { failtext ~= qformat("\n  "[], i, ": "[], t); }
    t2.failparse(failtext);
  }
  PlaceholderToken extra;
  Expr exEx, exBind;
  if (t2.accept("extra"[])) {
    if (!rest(t2, "tree.expr"[], &exEx))
      t2.failparse("Couldn't match extra"[]);
    extra = fastalloc!(PlaceholderTokenLV)(exEx.valueType(), "exEx.valueType()"[]);
    if (auto dc = fastcast!(DontCastMeExpr) (exEx))
      exBind = fastalloc!(DontCastMeExpr)(extra); // propagate outwards
    else
      exBind = extra;
  }
  if (!t2.accept(":"[]))
    t2.failparse("Expected ':'"[]);
  
  auto it = fastcast!(Iterator) (sub.valueType());
  auto ph = fastalloc!(PlaceholderToken)(it.elemType(), "it.elemType() "~ivarname);
  
  auto backup = namespace();
  auto mns = fastalloc!(MiniNamespace)("!safecode for_iter_var"[]);
  with (mns) {
    sup = backup;
    internalMode = true;
    if (ivarname) add(ivarname, ph);
    if (extra)    add("extra"[], exBind);
  }
  namespace.set(mns);
  scope(exit) namespace.set(backup);
  
  auto sc = new Scope;
  sc.configPosition(t2);
  namespace.set(sc);
  
  auto tmain = t2;
  if (!rest(t2, "tree.expr"[], &main))
    t2.failparse("Cannot parse iterator expression"[]);
  if (!t2.accept("]"[]))
    t2.failparse("Expected ']', partial is "[], main.valueType());
  text = t2;
  Expr res;
  PTuple!(IType, Expr, PlaceholderToken, PlaceholderToken) ipt;
  Iterator restype;
  if (auto ri = fastcast!(RichIterator) (it)) {
    auto foriter = new ForIter!(RichIterator);
    foriter.autofree = autofree;
    with (foriter) ipt = ptuple(wrapper, ex, var, extra);
    foriter.itertype = ri;
    restype = foriter;
  } else {
    auto foriter = new ForIter!(Iterator);
    foriter.autofree = autofree;
    with (foriter) ipt = ptuple(wrapper, ex, var, extra);
    foriter.itertype = it;
    restype = foriter;
  }
  auto str = fastalloc!(Structure)(cast(string) null);
  fastalloc!(RelMember)("subiter"[], sub.valueType(), str);
  fastalloc!(RelMember)("var"[], it.elemType(), str);
  if (extra) fastalloc!(RelMember)("extra"[], extra.valueType(), str);
  Expr[] field;
  field ~= sub;
  field ~= fastalloc!(Filler)(it.elemType());
  if (extra) field ~= exEx;
  ipt = stuple(str, fastalloc!(ScopeAndExpr)(sc, main), ph, extra);
  return fastcast!(Object)~ reinterpret_cast(fastcast!(IType)~ restype, fastalloc!(StructLiteral)(str, field));
}
mixin DefaultParser!(gotForIter, "tree.expr.iter.for"[], null, "["[]);
static this() {
  addPrecedence("tree.expr.iter"[], "441"[]);
}

LValue getRefExpr(Expr ex) {
  if (auto lv = fastcast!(LValue) (ex)) return lv;
  if (auto sae = fastcast!(StatementAndExpr) (ex)) {
    auto lv2 = getRefExpr(sae.second);
    if (!lv2) return null;
    return fastalloc!(StatementAndLValue)(sae.first, lv2);
  }
  return null;
}

extern(C) void rt_print(LLVMFile lf, string s);

class IterLetCond(T) : Cond, NeedsConfig {
  T target;
  Expr iter;
  LValue iref;
  Expr iref_pre;
  LValue address_target;
  this() { }
  this(T target, Expr iter, Expr iref_pre, LValue address_target) {
    this.target = target;
    this.iter = iter;
    this.iref_pre = iref_pre;
    this.address_target = address_target;
  }
  mixin DefaultDup!();
  mixin defaultIterate!(iter, target, iref, iref_pre);
  mixin defaultCollapse!();
  override void configure() { iref = lvize(iref_pre); }
  override void jumpOn(LLVMFile lf, bool cond, string dest) {
    mixin(mustOffset("0"));
    if (!iref) {
      logln("in iter cond ", this);
      breakpoint;
      fail("iter cond not configured");
    }
    auto itype = fastcast!(Iterator) (resolveType(iter.valueType()));
    auto stepcond = itype.testAdvance(iref);
    auto value = itype.currentValue(iref);
    auto skip = lf.allocLabel("iterletcond_skip");
    // TODO check if actually necessary!
    // opt(stepcond);
    // opt(value);
    if (cond) {
      // if jump fails, value is available; write it, then jump
      stepcond.jumpOn(lf, false, skip);
    } else {
      stepcond.jumpOn(lf, false, dest);
    }
    if (target) {
      auto tv = target.valueType;
      if (!gotImplicitCast(value, tv, (IType it) { return test(it == tv); }))
        fail;
      if (address_target) {
        auto lv = getRefExpr(value);
        if (!lv) throw new Exception(Format("Iterator "[], itype, " does not offer reference iteration: "[], value));
        emitAssign(lf, address_target, fastalloc!(RefExpr)(lv));
      } else {
        static if (is(T: MValue))
          (fastalloc!(_Assignment!(MValue))(target, value)).emitLLVM(lf);
        else emitAssign(lf, target, value);
      }
    } else {
      value.emitLLVM(lf);
      lf.pop();
    }
    if (cond) {
      jump(lf, dest);     // now jump
      lf.emitLabel(skip); // otherwise nothing
    }
  }
  override string toString() {
    if (target) return Format(target, " <- "[], iter);
    else return Format("test "[], iter);
  }
}

Object gotIterCond(bool expressionTargetAllowed = true)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue lv;
  MValue mv;
  string[] newVarNames; IType newVarType;
  bool needIterator;
  bool isRefDecl;
  const string myTE = "tree.expr _tree.expr.bin _tree.expr.iter_loose";
  bool wantTargetDecl = true;
  if (expressionTargetAllowed) {
    Object obj;
    auto t3 = t2;
    if (rest(t3, myTE, &obj)) {
      lv = fastcast!(LValue) (obj);
      mv = fastcast!(MValue) (obj);
      if (lv && fastcast!(Iterator) (lv.valueType())) lv = null;
      if (mv && fastcast!(Iterator) (mv.valueType())) mv = null;
      if (lv || mv) {
        wantTargetDecl = false;
        t2 = t3;
      }
    }
  }
  if (wantTargetDecl) {
    if (!expressionTargetAllowed) {
      // it's waay too early to commit to trying to parse a type!
      // maybe we can guess if we need to?
      auto t3 = t2;
      auto test = t3.slice("<-");
      if (test.find(";") != -1)
        return null; // this is PROBABLY safe
    }
    if (t2.accept("ref"[])) isRefDecl = true;
    else if (!t2.accept("auto"[])) {
      auto terrible_performance_improvement_hack = t2.between("", ";").find("<-") == -1;
      if (terrible_performance_improvement_hack || !rest(t2, "type"[], &newVarType))
        goto withoutIterator;
    }
    string newVarName;
    if (t2.gotIdentifier(newVarName)) {
      newVarNames ~= newVarName;
    } else if (t2.accept("(")) {
      while (t2.gotIdentifier(newVarName)) {
        newVarNames ~= newVarName;
        if (t2.accept(")")) break;
        if (t2.accept(",")) continue;
        return null;
      }
      if (!newVarNames.length) return null;
    } else goto withoutIterator;
  }
  if (!t2.acceptLeftArrow())
    return null;
  needIterator = true;
withoutIterator:
  if (!needIterator) return null;
  Expr iter;
  resetError();
  
  {
    auto backup = *templInstOverride.ptr();
    scope(exit) *templInstOverride.ptr() = backup;
    
    IType ty;
    if (lv) ty = lv.valueType();
    else if (mv) ty = mv.valueType();
    else if (newVarType) ty = newVarType;
    
    if (ty) *templInstOverride.ptr() = stuple(t2, ty);
    
    if (!rest(t2, "tree.expr >tree.expr.bin"[], &iter)) {
      
      if (needIterator) t2.failparse("Can't parse iterator"[]);
      else return null;
    }
  }
  
  auto backup = iter;
  
  if (!needIterator && !fastcast!(Iterator) (iter.valueType())) return null;
  
  if (!gotImplicitCast(iter, Single!(HintType!(Iterator)), (IType it) { return !!fastcast!(Iterator) (it); }))
    if (!needIterator) return null;
    else t2.failparse("Expected an iterator, not a "[], backup, " of ", backup.valueType());
  
  // insert declaration into current scope.
  // NOTE: this here is the reason why everything that tests a cond has to have its own scope.
  auto sc = fastcast!(Scope)~ namespace();
  // if (!sc) throw new Exception("Bad place for an iter cond: "~Format(namespace())~"!"[]);
  if (!sc) return null;
  
  LValue address_target;
  
  if (newVarNames) {
    bool makeTuple = newVarNames.length > 1;
    if (newVarType) {
      if (makeTuple) {
        IType[] repeated;
        foreach (name; newVarNames) repeated ~= newVarType;
        newVarType = mkTuple(repeated);
      }
    } else {
      newVarType = (fastcast!(Iterator) (resolveType(iter.valueType()))).elemType();
    }
    auto tup = fastcast!(Tuple) (newVarType);
    if (makeTuple) {
      if (!tup) {
        text.failparse("Iterating into tuple but iterator base type is ", newVarType);
      }
      if (tup.types().length != newVarNames.length) {
        text.failparse("Iterating into tuple but base type ",
          newVarType, " doesn't match tuple size ", newVarNames.length);
      }
    }
    
    string newVarName;
    if (newVarNames.length == 1) newVarName = newVarNames[0];
    
    Variable newvar;
    if (isRefDecl) {
      auto ty = fastalloc!(Pointer)(newVarType);
      newvar = fastalloc!(Variable)(ty, framelength(), cast(string) null);
      sc.add(newvar); // still need to add the variable for stackframe layout purposes
      lv = fastalloc!(DerefExpr)(newvar);
      address_target = newvar;
      if (newVarName)
        sc.add(fastalloc!(LValueAlias)(lv, newVarName));
    } else {
      newvar = fastalloc!(Variable)(newVarType, framelength(), newVarName);
      sc.add(newvar);
      lv = newvar;
    }
    auto newdecl = fastalloc!(VarDecl)(newvar);
    newdecl.initInit();
    sc.addStatement(newdecl);
    
    if (makeTuple) {
      foreach (i, name; newVarNames) {
        sc.add(fastalloc!(LValueAlias)(mkTupleIndexAccess(
          lv, i, true
        ), name));
      }
    }
  }
  
  Expr ex;
  if (lv) ex = lv; else ex = mv;
  if (ex) { // yes, no-variable iteration is possible.
    auto vt = ex.valueType(), it = fastcast!(Iterator) (resolveType(iter.valueType())), et = it.elemType();
    Expr temp = fastalloc!(Placeholder)(fastcast!(IType)~ et);
    if (!gotImplicitCast(temp, (IType it) { return test(it == vt); })) {
      logln(text.nextText());
      text.failparse("Can't iterate "[], it, " (elem type "[], et, "[]), into variable of "[],  vt);
    }
  }
  
  text = t2;
  
  if (lv) return fastcast!(Object)(
    cond2ex(fastalloc!(IterLetCond!(LValue))(lv, iter, iter, address_target)));
  else return fastcast!(Object)(
    cond2ex(fastalloc!(IterLetCond!(MValue))(mv, iter, iter, address_target)));
}
mixin DefaultParser!(gotIterCond!(false), "tree.expr.iter_strict"[], "121"[]);
mixin DefaultParser!(gotIterCond!(true), "tree.expr.iter_loose"[], "220"[]);

HintType!(Iterator) anyIteratorTypeHint;

void setupIterIndex() {
  implicits ~= delegate Expr(Expr ex) {
    if (!fastcast!(Iterator) (ex.valueType())) return null;
    return cond2ex(fastalloc!(IterLetCond!(LValue))
      (cast(LValue)null, ex, ex, cast(LValue)null));
  };
  defineOp("index"[], delegate Expr(Expr e1, Expr e2) {
    if (!anyIteratorTypeHint) New(anyIteratorTypeHint);
    if (!gotImplicitCast(e1, anyIteratorTypeHint, (IType it) {
      return test(fastcast!(Iterator) (resolveType(it)));
    })) return null;
    auto iter = fastcast!(Iterator) (resolveType(e1.valueType()));
    auto ri = fastcast!(RichIterator) (iter);
    if (!ri)
      throw new Exception(Format("Cannot access by index; not a rich iterator! "[]));
    if (auto rish = fastcast!(RangeIsh) (e2.valueType())) {
      auto from = rish.getPos(e2), to = rish.getEnd(e2);
      return ri.slice(e1, from, to);
    } else {
      return ri.index(e1, e2);
    }
  });
}

// Statement with target, Expr without. Lol.
class EvalIterator(T) : Expr, Statement {
  Expr ex;
  T iter;
  Expr target; // optional
  private this() { }
  this(Expr ex, T t) {
    this.ex = ex;
    this.iter = t;
    // prime the template!
    // auto eaType = fastalloc!(ExtArray)(iter.elemType(), true);
    // BEWARNED: commenting this in will expose a highly nasty bug that I've been unable to solve. Good luck and godspeed.
    // iparse!(Statement, "prime_that_template"[], "tree.stmt"[])(`{ auto qwenya = ex; T gob; type-of __istep qwenya foo; gob ~= foo; }`, "ex"[], ex, "T"[], eaType);
  }
  this(Expr ex, T t, Expr target) {
    this(ex, t);
    this.target = target;
  }
  EvalIterator dup() {
    auto res = new EvalIterator;
    res.ex = ex.dup;
    res.iter = iter;
    res.target = target;
    return res;
  }
  mixin defaultIterate!(ex, target);
  mixin defaultCollapse!();
  override {
    IType valueType() {
      if (Single!(Void) == iter.elemType())
        return Single!(Void);
      else
        static if (is(T == RichIterator))
          return fastalloc!(Array)(iter.elemType());
        else
          return fastalloc!(ExtArray)(iter.elemType(), true);
    }
    string toString() { return Format("Eval("[], ex, ")"[]); }
    void emitLLVM(LLVMFile lf) {
      int offs;
      void emitStmtInto(Expr var, Expr ex2 = null, bool checkArray = true) {
        if (!ex2) ex2 = ex;
        auto lv = fastcast!(LValue) (ex2);
        if (lv && var) {
          iparse!(Statement, "iter_array_eval_step_1"[], "tree.stmt"[])
                 (` { int i; while var[i++] <- _iter { } }`,
                  namespace(), "var"[], checkArray?var:getArrayPtr(var), "_iter"[], lv).emitLLVM(lf);
        } else if (var) {
          iparse!(Statement, "iter_array_eval_step_2"[], "tree.stmt"[])
                 (` { int i; auto temp = _iter; while var[i++] <- temp { } }`,
                  namespace(), "var"[], checkArray?var:getArrayPtr(var), "_iter"[], ex2).emitLLVM(lf);
        } else {
          iparse!(Statement, "iter_eval_step_3"[], "tree.stmt"[])
                 (` { auto temp = _iter; while temp { } }`,
                  namespace(), "_iter"[], ex2).emitLLVM(lf);
        }
      }
      void emitStmtConcat(Expr var) {
        if (auto lv = fastcast!(LValue)~ ex) {
          iparse!(Statement, "iter_array_eval_step_4"[], "tree.stmt"[])
                 (` { type-of-elem _iter temp; while temp <- _iter { var ~= temp; } }`,
                  namespace(),
                  "var"[], var, "_iter"[], lv).emitLLVM(lf);
        } else if (var) {
          iparse!(Statement, "iter_array_eval_step_5"[], "tree.stmt"[])
                 (` { auto temp = _iter; type-of-elem temp temp2; while temp2 <- temp { var ~= temp2; } }`,
                  namespace(),
                  "var"[], var, "_iter"[], ex).emitLLVM(lf);
        } else {
          iparse!(Statement, "iter_eval_step_6"[], "tree.stmt"[])
                 (` { auto temp = _iter; while temp { } }`,
                  "_iter"[], ex).emitLLVM(lf);
        }
      }
      if (target) {
        emitStmtInto(target);
      } else {
        if (Single!(Void) == valueType())
          emitStmtInto(null);
        else {
          static if (is(T == RichIterator)) {
            auto var = fastalloc!(LLVMRef)(valueType());
            var.allocate(lf);
            var.begin(lf);
            scope(success) {
              var.emitLLVM(lf);
              var.end(lf);
            }
            auto lv = fastalloc!(LLVMRef)(ex.valueType());
            lv.allocate(lf);
            lv.begin(lf);
            scope(success) lv.end(lf);
            
            emitAssign(lf, lv, ex);
            iparse!(Statement, "initVar"[], "tree.semicol_stmt.assign"[])
                    (`var = new elem[] len`,
                    "var"[], var, "len"[], iter.length(lv), "elem"[], iter.elemType()).emitLLVM(lf);
            // buildFunCall(sysmod.lookup("printf"), mkTupleExpr(mkString("var (%i, %p) = new elem[] %i due to "~qformat(iter)~" and len "~qformat(iter.length(lv))~"\n"), var, iter.length(lv)), "printf").emitLLVM(lf); lf.pop();
            emitStmtInto(var, lv, false);
          } else {
            auto ea = fastalloc!(ExtArray)(iter.elemType(), true);
            auto var = fastalloc!(LLVMRef)(ea);
            var.allocate(lf);
            var.begin(lf);
            emitAssign(lf, var, fastalloc!(ZeroInitializer)(ea));
            emitStmtConcat(var);
            var.emitLLVM(lf);
            var.end(lf);
          }
        }
      }
    }
  }
}

Object gotIterEvalTail(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, Single!(HintType!(Iterator)), (IType it) {
      return !!fastcast!(Iterator) (resolveType(it)); 
    })) return null;
    auto iter = fastcast!(Iterator) (resolveType(ex.valueType()));
    if (auto ri = fastcast!(RichIterator)~ iter) {
      return new EvalIterator!(RichIterator) (ex, ri);
    } else {
      return new EvalIterator!(Iterator) (ex, iter);
    }
  };
}
mixin DefaultParser!(gotIterEvalTail, "tree.rhs_partial.iter_eval"[], null, ".eval"[]);

static this() {
  defineOp("length"[], delegate Expr(Expr ex) {
    auto iter = fastcast!(RichIterator) (ex.valueType());
    if (!iter) return null;
    return iter.length(ex);
  });
}

import tools.log;
Object gotIteratorAssign(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr target;
  if (rest(t2, "tree.expr _tree.expr.bin"[], &target) && t2.accept("="[])) {
    Expr value;
    if (!rest(t2, "tree.expr"[], &value) || !gotImplicitCast(value, Single!(HintType!(Iterator)), (IType it) {
      auto ri = fastcast!(RichIterator)~ it;
      return ri && target.valueType() == fastalloc!(Array)(ri.elemType());
    })) {
      // don't - this messes up the error of standard assignment!
      // text.setError("Mismatching types in iterator assignment: "[], target, " <- "[], value.valueType());
      return null;
    }
    text = t2;
    auto it = fastcast!(RichIterator)~ value.valueType();
    return new EvalIterator!(RichIterator) (value, it, target);
  } else return null;
}
mixin DefaultParser!(gotIteratorAssign, "tree.semicol_stmt.assign_iterator"[], "11"[]);

Object gotElemTypeOf(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  IType ty;
  if (!rest(t2, "tree.expr _tree.expr.bin"[], &ex))
    if (!rest(t2, "type"[], &ty))
      t2.failparse("Failed to parse type-of-elem"[]);
  
  Iterator it;
  if (ty) {
    ty = resolveType(ty);
    Expr pt = fastalloc!(PlaceholderToken)(ty, "elem-type-of temp"[]);
    if (!gotImplicitCast(pt, Single!(HintType!(Iterator)), (IType it) { return !!fastcast!(Iterator) (it); }))
      text.failparse("Expected iterator, not "[], ty);
    it = fastcast!(Iterator) (pt.valueType());
  } else {
    if (!gotImplicitCast(ex, Single!(HintType!(Iterator)), (IType it) { return !!fastcast!(Iterator) (it); }))
      text.failparse("Expected iterator, not "[], ex.valueType());
    it = fastcast!(Iterator) (ex.valueType());
  }
  
  text = t2;
  return fastcast!(Object) (it.elemType());
}
mixin DefaultParser!(gotElemTypeOf, "type.of_elem"[], "450"[], "type-of-elem"[]);
