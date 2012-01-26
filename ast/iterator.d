module ast.iterator;

import ast.base, ast.parse, ast.types, ast.namespace, ast.structure, ast.casting, ast.pointer;

interface Iterator {
  IType elemType();
  Cond testAdvance(LValue); // false => couldn't get a value
  Expr currentValue(Expr);
}

interface RichIterator : Iterator {
  Expr length(Expr);
  Expr index(Expr, Expr pos);
  Expr slice(Expr, Expr from, Expr to);
}

interface RangeIsh {
  Expr getPos(Expr base);
  Expr getEnd(Expr base);
}

class Range : Type, RichIterator, RangeIsh {
  IType wrapper;
  LValue castToWrapper(LValue lv) {
    return iparse!(LValue, "range_cast_to_wrapper", "tree.expr")
                  ("*wrapper*:&lv", "lv", lv, "wrapper", wrapper);
  }
  Expr castExprToWrapper(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex)
      return castToWrapper(lv);
    return reinterpret_cast(wrapper, ex);
  }
  override {
    IType elemType() { return mkMemberAccess(new ast.base.Placeholder(wrapper), "cur").valueType(); }
    string toString() { return Format("RangeIter[", size, "](", wrapper, ")"); }
    int size() { return wrapper.size; }
    string mangle() { return "range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr currentValue(Expr ex) {
      return mkMemberAccess(castExprToWrapper(ex), "cur");
    }
    import ast.conditionals: Compare;
    Cond testAdvance(LValue lv) {
      return iparse!(Cond, "test_advance_range", "cond")
                    ("++lv.cur != lv.end", "lv", castToWrapper(lv));
    }
    Expr length(Expr ex) {
      return iparse!(Expr, "length_range", "tree.expr")
                    ("int:(ex.end - ex.cur - 1)", "ex", castExprToWrapper(ex));
    }
    Expr index(Expr ex, Expr pos) {
      return iparse!(Expr, "index_range", "tree.expr")
                    ("ex.cur + pos",
                     "ex", castExprToWrapper(ex),
                     "pos", pos);
    }
    Expr slice(Expr ex, Expr from, Expr to) {
      return iparse!(Expr, "slice_range", "tree.expr")
                    ("(ex.cur + from) .. (ex.cur + to)",
                     "ex", castExprToWrapper(ex),
                     "from", from, "to", to);
    }
    // DOES NOT HONOR ITERATOR SEMANTICS!!
    Expr getPos(Expr ex) {
      return lookupOp("+", mkInt(1), mkMemberAccess(castExprToWrapper(ex), "cur"));
    }
    Expr getEnd(Expr ex) {
      return mkMemberAccess(castExprToWrapper(ex), "end");
    }
  }
}

import ast.int_literal;
class ConstIntRange : Type, RichIterator, RangeIsh {
  int from, to;
  this(int f, int t) { this.from = f; this.to = t; }
  override {
    IType elemType() { return Single!(SysInt); }
    string toString() { return Format("ConstIntRange[", size, "]()"); }
    int size() { return nativeIntSize; }
    string mangle() { return Format("constint_range_", from, "_to_", to).replace("-", "_minus_"); }
    ubyte[] initval() { return cast(ubyte[]) (&from)[0..1]; }
    Expr currentValue(Expr ex) {
      return reinterpret_cast(Single!(SysInt), ex);
    }
    import ast.conditionals: Compare;
    Cond testAdvance(LValue lv) {
      return iparse!(Cond, "test_advance_int_range", "cond")
                    ("++lv != to",
                     "lv", reinterpret_cast(Single!(SysInt), lv),
                     "to", mkInt(to)
                    );
    }
    Expr length(Expr ex) {
      return iparse!(Expr, "const_int_length", "tree.expr")
                    (`to - ex - 1`,
                     "ex", reinterpret_cast(Single!(SysInt), ex),
                     "to", new IntExpr(to));
    }
    Expr index(Expr ex, Expr pos) {
      return iparse!(Expr, "const_index_range", "tree.expr")
                    ("ex + 1 + pos",
                     "ex", reinterpret_cast(Single!(SysInt), ex),
                     "pos", pos);
    }
    Expr slice(Expr ex, Expr from, Expr to) {
      // TODO specialize for int from, to
      return iparse!(Expr, "slice_range", "tree.expr")
                    ("(ex + from) .. (ex + to)",
                     "ex", reinterpret_cast(Single!(SysInt), ex),
                     "from", from, "to", to);
    }
    // behaves differently from the iterator interface!!
    Expr getPos(Expr ex) {
      return lookupOp("+", mkInt(1), reinterpret_cast(Single!(SysInt), ex));
    }
    Expr getEnd(Expr ex) { return mkInt(to); }
  }
}

Expr mkRange(Expr from, Expr to) {
  auto wrapped = new Structure(null);
  // cur must start one early
  auto fvt = from.valueType();
  from = lookupOp("-", from, mkInt(1));
  if (!gotImplicitCast(from, fvt, (IType it) { return !!(it == fvt); }) && !(from = tryConvert(from, fvt), from))
    throw new Exception(Format("mkRange: ", fvt, " does not cleanly implement integer subtraction or allow down-conversion. "));
  new RelMember("cur", from.valueType(), wrapped);
  new RelMember("end", to.valueType(), wrapped);
  auto range = new Range;
  range.wrapper = wrapped;
  return new RCE(range, new StructLiteral(wrapped, [from, to]));
}

import ast.tuples, ast.literal_string;
Object gotRangeIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr from, to;
  auto t2 = text;
  if (!cont(t2, &from)) return null;
  if (!t2.accept("..")) return null;
  if (!cont(t2, &to))
    t2.failparse("Unable to acquire second half of range def");
  text = t2;
  bool notATuple(IType it) { return !fastcast!(Tuple) (it); }
  bool isByte(IType it) { return !!fastcast!(Byte) (it); }
  gotImplicitCast(from, &notATuple);
  gotImplicitCast(to  , &notATuple);
  from = foldex(from); to = foldex(to);
  if (auto sl = fastcast!(StringExpr) (from)) if (sl.str.length == 1) gotImplicitCast(from, &isByte);
  if (auto sl = fastcast!(StringExpr) (to))   if (sl.str.length == 1) gotImplicitCast(to,   &isByte);
  auto ifrom = fastcast!(IntExpr)~ fold(from), ito = fastcast!(IntExpr)~ fold(to);
  if (ifrom && ito)
    return fastcast!(Object)~ reinterpret_cast(new ConstIntRange(ifrom.num, ito.num), mkInt(ifrom.num - 1));
  return fastcast!(Object)~ mkRange(from, to);
}
mixin DefaultParser!(gotRangeIter, "tree.expr.iter_range", "11");

class StructIterator : Type, Iterator {
  IType wrapped;
  IType _elemType;
  this(IType it) {
    wrapped = it;
    scope(failure) fail;
    scope(failure) logln("it was ", it);
    _elemType = iparse!(Expr, "si_elemtype", "tree.expr.eval")
                       (`evaluate (bogus.value)`,
                        "bogus", new PlaceholderTokenLV(wrapped, "wrapped")
                       ).valueType();
  }
  override {
    int size() { return wrapped.size; }
    string mangle() { return "struct_iterator_"~wrapped.mangle(); }
    ubyte[] initval() { return wrapped.initval; }
    IType elemType() { return _elemType; }
    Expr currentValue(Expr ex) {
      ex = reinterpret_cast(wrapped, ex);
      return iparse!(Expr, "si_value", "tree.expr")
                    (`evaluate (ex.value)`,
                     "ex", ex);
    }
    Cond testAdvance(LValue lv) {
      lv = fastcast!(LValue) (reinterpret_cast(wrapped, lv));
      return iparse!(Cond, "si_ivalid", "cond")
                    (`evaluate (lv.advance)`,
                     "lv", lv);
    }
    string toString() { return Format("si ", wrapped); }
  }
}

static this() {
  /*implicits ~= delegate Expr(Expr ex) {
    if (auto si = fastcast!(StructIterator) (ex.valueType())) {
      return reinterpret_cast(si.wrapped, ex);
    }
    return null;
  };*/
}

import tools.base: This, This_fn, rmSpace, PTuple, Stuple, ptuple, stuple;

import ast.fold, ast.conditionals;
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
    return iparse!(LValue, "foriter_cast_to_wrapper", "tree.expr")
                  ("*wrapper*:&lv", "lv", lv, "wrapper", wrapper);
  }
  Expr castToWrapper(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex) return castToWrapper(lv);
    return iparse!(Expr, "foriter_cast_ex_to_wrapper", "tree.expr")
                  ("wrapper:ex", "ex", ex, "wrapper", wrapper);
  }
  LValue subexpr(LValue lv) {
    return iparse!(LValue, "foriter_get_subexpr_lv", "tree.expr")
                  ("lv.subiter", "lv", lv);
  }
  Expr subexpr(Expr ex) {
    if (auto lv = fastcast!(LValue)~ ex) return subexpr(lv);
    opt(ex);
    // optimize subexpr of literal
    auto res = iparse!(Expr, "foriter_get_subexpr", "tree.expr")
                      ("ex.subiter", "ex", ex);
    opt(res);
    return res;
  }
  import ast.literal_string;
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
    // The whole substmap business is major hax.
    // basically I'm doing this because I can't work out why
    // my recursion keeps going cyclical,
    // and this is a haphazard way of breaking the cycle.
    // If you have to maintain this for whatever reason, don't even try.
    // Throw it out and start over.
    // Or pray your error isn't in the next bit, because God knows I have no idea why it works.
    IType[IType] substmap;
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
            if (auto p = fi in substmap) {
              it = fastcast!(Iterable)~ reinterpret_cast(*p, ex);
              return;
            }
            auto fi2 = fi.dup;
            substmap[fi] = fi2;
            substmap[fi2] = fi2; // what why FFUUUU
            add(fi2.ex);
            ex.iterate(&subst);
            it = fastcast!(Iterable)~ reinterpret_cast(fi2, ex);
            return;
          } else if (auto fi = fastcast!(ForIter!(Iterator)) (ex.valueType())) {
            ex = resolveRC(ex);
            if (auto p = fi in substmap) {
              it = fastcast!(Iterable)~ reinterpret_cast(*p, ex);
              return;
            }
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
        logln("wtf?! didn't I do ", cur_ex, " already?");
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
    auto var = iparse!(Expr, "foriter_ex_var_lookup", "tree.expr")
                      ("iex.var", "iex", iex);
    ex = update(ex, this.var, var);
    if (this.extra) {
      auto extra = iparse!(Expr, "foriter_ex_extra_lookup", "tree.expr")
                      ("iex.extra", "iex", iex);
      ex = update(ex, this.extra, extra);
    }
    return ex;
  }
  Statement mkForIterAssign(LValue lv, ref LValue wlv) {
    wlv = castToWrapper(lv);
    auto var = iparse!(LValue, "foriter_wlv_var", "tree.expr")
                      ("wlv.var", "wlv", wlv);
    return new Assignment(var, itertype.currentValue(subexpr(wlv.dup)));
  }
  override {
    string toString() {
      auto sizeinfo = Format(size, ":");
      (fastcast!(Structure)~ wrapper).select((string, RelMember rm) { sizeinfo ~= Format(" ", rm.type.size); });
      return Format("ForIter[", sizeinfo, "](", itertype, ": ", ex.valueType(), ") var ", cast(void*) var, " extra ", cast(void*) extra);
    }
    IType elemType() { return ex.valueType(); }
    int size() { return wrapper.size; }
    string mangle() { return Format("for_range_over_", wrapper.mangle(), "_var_", cast(size_t) var, "_extra_", cast(size_t) extra); }
    ubyte[] initval() { return wrapper.initval(); }
    Cond testAdvance(LValue lv) {
      auto res = itertype.testAdvance(subexpr(castToWrapper(lv).dup));
      if (autofree) {
        // res || ('ex.subiter.extra.free', false)
        // logln("btw 1 ex is type ", subexpr(castToWrapper(lv)).valueType());
        auto fi = fastcast!(ForIter!(RichIterator)) (subexpr(castToWrapper(lv)).valueType());
        auto sub = fi.castToWrapper(subexpr(castToWrapper(lv)));
        // logln("auto-free() of type ", iparse!(Expr, "mew", "tree.expr")(`ex.extra`, "ex", sub).valueType());
        Statement freest = iparse!(Statement, "autofree_exec", "tree.stmt")
                                  (`ex.extra.free();`, "ex", sub);
        res = new OrOp(res, new StatementAndCond(freest, cFalse));
      }
      return res;
    }
    Expr currentValue(Expr ex) {
      auto lv = fastcast!(LValue) (ex);
      if (!lv) {
        logln("TODO: mandate lvalue for curval");
        fail;
      }
      LValue wlv;
      auto stmt = mkForIterAssign(lv, wlv);
      return new StatementAndExpr(stmt, update(this.ex.dup, wlv));
    }
    static if (is(I: RichIterator)) {
      Expr length(Expr ex) {
        return itertype.length(subexpr(castToWrapper(ex).dup));
      }
      Expr index(Expr ex, Expr pos) {
        auto we = castToWrapper(ex);
        auto st = new Structure(null);
        new RelMember("var", var.valueType(), st);
        Expr tup;
        if (extra) {
          new RelMember("extra", extra.valueType(), st);
          tup = mkTupleExpr(
            itertype.index(subexpr(we.dup), pos),
            mkMemberAccess(we, "extra")
          );
        } else {
          tup = mkTupleExpr(
            itertype.index(subexpr(we.dup), pos)
          );
        }
        auto casted = reinterpret_cast(st, tup);
        return update(this.ex.dup, casted);
      }
      Expr slice(Expr ex, Expr from, Expr to) {
        auto wr = castToWrapper(ex);
        Expr[] field = [fastcast!(Expr)~ itertype.slice(subexpr(wr.dup), from, to),
                        new Filler(itertype.elemType())];
        if (extra) field ~= extra;
        return new RCE(this,
          new StructLiteral(fastcast!(Structure)~ wrapper, field));
      }
    }
  }
}

import ast.scopes;
class ScopeAndExpr : Expr {
  Scope sc;
  Expr ex;
  this(Scope sc, Expr ex) { this.sc = sc; this.ex = ex; }
  mixin defaultIterate!(sc, ex);
  override {
    string toString() { return Format("sae(", sc._body, ", ", ex, ")"); }
    ScopeAndExpr dup() { return new ScopeAndExpr(sc.dup, ex.dup); }
    IType valueType() { return ex.valueType(); }
    void emitAsm(AsmFile af) {
      // logln("emit ", this);
      // dirty, dirty hackaround (!)
      // TODO: discover why the fuck this what wtf help
      sc._body = Single!(AggrStatement);
      sc.id = getuid();
      if (Single!(Void) == ex.valueType()) {
        mixin(mustOffset("0"));
        auto dg = sc.open(af)();
        ex.emitAsm(af);
        dg();
      } else {
        mixin(mustOffset("ex.valueType().size"));
        mkVar(af, ex.valueType(), true, (Variable var) {
          auto dg = sc.open(af)();
          (new Assignment(var, ex)).emitAsm(af);
          dg();
        });
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

import ast.static_arrays;

class BogusIterator : Iterator, IType { // tag
  override {
    IType elemType() { assert(false); }
    Expr currentValue(Expr) { assert(false); }
    Cond testAdvance(LValue) { assert(false); }
    int size() { assert(false); }
    string mangle() { assert(false); }
    ubyte[] initval() { assert(false); }
    int opEquals(IType it) { assert(false); }
    IType proxyType() { assert(false); }
    bool isPointerLess() { assert(false); }
    bool isComplete() { assert(false); }
  }
}

import ast.aggregate, ast.literals: DataExpr;
Object gotForIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr sub, main;
  auto t2 = text;
  
  bool autofree;
  if (t2.accept("auto") && t2.accept("~")) autofree = true;
  
  if (!t2.accept("for")) return null;
  
  string ivarname;
  auto t3 = t2;
  if (t3.gotIdentifier(ivarname) && t3.accept("<-")) {
    t2 = t3;
  } else ivarname = null;
  if (!rest(t2, "tree.expr", &sub))
    t2.failparse("Cannot find sub-iterator");
  auto subx = sub;
  IType[] tried;
  if (!gotImplicitCast(sub, Single!(BogusIterator), (Expr ex) { tried ~= ex.valueType(); return !!fastcast!(Iterator) (ex.valueType()); })) {
    string failtext = "Invalid sub-iterator: none of these are iterators: ";
    foreach (i, t; tried) { failtext ~= qformat("\n  ", i, ": ", t); }
    t2.failparse(failtext);
  }
  PlaceholderToken extra;
  Expr exEx, exBind;
  if (t2.accept("extra")) {
    if (!rest(t2, "tree.expr", &exEx))
      t2.failparse("Couldn't match extra");
    extra = new PlaceholderTokenLV(exEx.valueType(), "exEx.valueType()");
    if (auto dc = fastcast!(DontCastMeExpr) (exEx))
      exBind = new DontCastMeExpr(extra); // propagate outwards
    else
      exBind = extra;
  }
  if (!t2.accept(":"))
    t2.failparse("Expected ':'");
  
  auto it = fastcast!(Iterator) (sub.valueType());
  auto ph = new PlaceholderToken(it.elemType(), "it.elemType() "~ivarname);
  
  auto backup = namespace();
  auto mns = new MiniNamespace("!safecode for_iter_var");
  with (mns) {
    sup = backup;
    internalMode = true;
    if (ivarname) add(ivarname, ph);
    if (extra)    add("extra", exBind);
  }
  namespace.set(mns);
  scope(exit) namespace.set(backup);
  
  auto sc = new Scope;
  sc.requiredDepth = int.max; // PROBABLY okay
  sc.configPosition(t2);
  namespace.set(sc);
  
  if (!rest(t2, "tree.expr", &main))
    t2.failparse("Cannot parse iterator expression");
  if (!t2.accept("]"))
    t2.failparse("Expected ']', partial is ", main.valueType());
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
  // This probably won't help any but I'm gonna do it anyway.
  Structure best;
  int[] bsorting;
  void tryIt(int[] sorting) {
    auto test = new Structure(null);
    void add(int i) {
      switch (i) {
        case 0: new RelMember("subiter", sub.valueType(), test); break;
        case 1: new RelMember("var", it.elemType(), test); break;
        case 2: new RelMember("extra", extra.valueType(), test); break;
      }
    }
    foreach (entry; sorting) add(entry);
    if (!best) { best = test; bsorting = sorting; }
    else if (test.size < best.size) { best = test; bsorting = sorting; }
  }
  if (extra) {
    foreach (tri; [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]])
      tryIt(tri);
  } else {
    tryIt([0, 1]);
    tryIt([1, 0]);
  }
  Expr[] field;
  void add(int i) {
    switch (i) {
      case 0: field ~= sub; break;
      case 1: field ~= new Filler(it.elemType()); break;
      case 2: field ~= exEx; break;
    }
  }
  foreach (entry; bsorting) add(entry);
  ipt = stuple(best, new ScopeAndExpr(sc, main), ph, extra);
  return fastcast!(Object)~ reinterpret_cast(fastcast!(IType)~ restype, new StructLiteral(best, field));
}
mixin DefaultParser!(gotForIter, "tree.expr.iter.for", null, "[");
static this() {
  parsecon.addPrecedence("tree.expr.iter", "441");
}

import ast.variable, ast.assign;
class IterLetCond(T) : Cond, NeedsConfig {
  T target;
  Expr iter;
  LValue iref;
  Expr iref_pre;
  this() { }
  this(T target, Expr iter, Expr iref_pre) {
    this.target = target;
    this.iter = iter;
    this.iref_pre = iref_pre;
  }
  mixin DefaultDup!();
  mixin defaultIterate!(iter, target, iref, iref_pre);
  override void configure() { iref = lvize(iref_pre); }
  override void jumpOn(AsmFile af, bool cond, string dest) {
    auto itype = fastcast!(Iterator) (resolveType(iter.valueType()));
    auto stepcond = itype.testAdvance(iref);
    auto value = itype.currentValue(iref);
    auto skip = af.genLabel();
    opt(stepcond);
    if (cond) {
      // if jump fails, value is available; write it, then jump
      stepcond.jumpOn(af, false, skip);
    } else {
      stepcond.jumpOn(af, false, dest);
    }
    if (target) {
      auto tv = target.valueType;
      if (!gotImplicitCast(value, tv, (IType it) { return test(it == tv); }))
        fail;
      static if (is(T: MValue))
        (new _Assignment!(MValue) (target, value)).emitAsm(af);
      else (new Assignment(target, value)).emitAsm(af);
    } else {
      value.emitAsm(af);
      if (value.valueType() != Single!(Void))
        af.sfree(value.valueType().size);
    }
    if (cond) {
      af.jump(dest); // now jump
      af.emitLabel(skip, !keepRegs, isForward); // otherwise nothing
    }
  }
  override string toString() {
    if (target) return Format(target, " <- ", iter);
    else return Format("test ", iter);
  }
}

import ast.scopes, ast.vardecl;

Object gotIterCond(bool withoutIteratorAllowed, bool expressionTargetAllowed = true)(ref string text, ParseCb cont, ParseCb rest) {
  static if (!expressionTargetAllowed)
    static assert(!withoutIteratorAllowed);
  auto t2 = text;
  LValue lv;
  MValue mv;
  string newVarName; IType newVarType;
  bool needIterator;
  const string myTE = "tree.expr _tree.expr.cond >tree.expr.arith";
  if (!expressionTargetAllowed || !rest(t2, myTE, &lv, (LValue lv) { return !fastcast!(Iterator) (lv.valueType()); })) {
    if (!expressionTargetAllowed || !rest(t2, myTE, &mv, (MValue mv) { return !fastcast!(Iterator) (mv.valueType()); })) {
      if (!t2.accept("auto") && !rest(t2, "type", &newVarType) || !t2.gotIdentifier(newVarName))
        goto withoutIterator;
    }
  }
  if (!t2.accept("<-"))
    return null;
  needIterator = true;
withoutIterator:
  if (!withoutIteratorAllowed && !needIterator) return null;
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
    
    if (!rest(t2, "tree.expr >tree.expr.cond", &iter)) {
      
      if (needIterator) t2.failparse("Can't parse iterator");
      else return null;
    }
  }
  
  auto backup = iter;
  
  if (!needIterator && !fastcast!(Iterator) (iter.valueType())) return null;
  
  if (!gotImplicitCast(iter, Single!(BogusIterator), (IType it) { return !!fastcast!(Iterator) (it); }))
    if (!needIterator) return null;
    else t2.failparse("Expected an iterator, not a ", backup);
  
  // insert declaration into current scope.
  // NOTE: this here is the reason why everything that tests a cond has to have its own scope.
  auto sc = fastcast!(Scope)~ namespace();
  // if (!sc) throw new Exception("Bad place for an iter cond: "~Format(namespace())~"!");
  if (!sc) return null;
  
  if (newVarName) {
    if (!newVarType) newVarType = (fastcast!(Iterator) (resolveType(iter.valueType()))).elemType();
    auto newvar = new Variable(newVarType, newVarName, boffs(newVarType));
    newvar.initInit();
    lv = newvar;
    sc.addStatement(new VarDecl(newvar));
    sc.add(newvar);
  }
  
  Expr ex;
  if (lv) ex = lv; else ex = mv;
  if (ex) { // yes, no-iterator iteration is possible.
    auto vt = ex.valueType(), it = fastcast!(Iterator) (resolveType(iter.valueType())), et = it.elemType();
    Expr temp = new Placeholder(fastcast!(IType)~ et);
    if (!gotImplicitCast(temp, (IType it) { return test(it == vt); })) {
      logln(text.nextText()); 
      text.failparse("Can't iterate ", it, " (elem type ", et, "), into variable of ",  vt);
    }
  }
  
  text = t2;
  
  if (lv) return new IterLetCond!(LValue) (lv, iter, iter);
  else return new IterLetCond!(MValue) (mv, iter, iter);
}
mixin DefaultParser!(gotIterCond!(false, false), "cond.iter_very_strict", "7050");
mixin DefaultParser!(gotIterCond!(false, true), "cond.iter_strict", "705");
mixin DefaultParser!(gotIterCond!(true), "cond.iter_loose", "735");

import ast.opers;
static this() {
  defineOp("index", delegate Expr(Expr e1, Expr e2) {
    if (!gotImplicitCast(e1, (IType it) {
      return test(fastcast!(Iterator) (resolveType(it)));
    })) return null;
    auto iter = fastcast!(Iterator) (resolveType(e1.valueType()));
    auto ri = fastcast!(RichIterator) (iter);
    if (!ri)
      throw new Exception(Format("Cannot access by index; not a rich iterator! "));
    if (auto rish = fastcast!(RangeIsh) (e2.valueType())) {
      auto from = rish.getPos(e2), to = rish.getEnd(e2);
      return ri.slice(e1, from, to);
    } else {
      return ri.index(e1, e2);
    }
  });
}

import ast.arrays, ast.modules, ast.aggregate;
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
    // auto eaType = new ExtArray(iter.elemType(), true);
    // BEWARNED: commenting this in will expose a highly nasty bug that I've been unable to solve. Good luck and godspeed.
    // iparse!(Statement, "prime_that_template", "tree.stmt")(`{ auto qwenya = ex; T gob; type-of __istep qwenya foo; gob ~= foo; }`, "ex", ex, "T", eaType);
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
  override {
    IType valueType() {
      if (Single!(Void) == iter.elemType())
        return Single!(Void);
      else
        static if (is(T == RichIterator))
          return new Array(iter.elemType());
        else
          return new ExtArray(iter.elemType(), true);
    }
    string toString() { return Format("Eval(", ex, ")"); }
    void emitAsm(AsmFile af) {
      int offs;
      void emitStmtInto(Expr var, Expr ex2 = null) {
        if (!ex2) ex2 = ex;
        auto lv = fastcast!(LValue) (ex2);
        if (lv && var) {
          iparse!(Statement, "iter_array_eval_step_1", "tree.stmt")
                 (` { int i; while var[i++] <- _iter { } }`,
                  "var", var, "_iter", lv, af).emitAsm(af);
        } else if (var) {
          iparse!(Statement, "iter_array_eval_step_2", "tree.stmt")
                 (` { int i; auto temp = _iter; while var[i++] <- temp { } }`,
                  "var", var, "_iter", ex2, af).emitAsm(af);
        } else {
          iparse!(Statement, "iter_eval_step_3", "tree.stmt")
                 (` { auto temp = _iter; while temp { } }`,
                  "_iter", ex2, af).emitAsm(af);
        }
      }
      void emitStmtConcat(Expr var) {
        if (auto lv = fastcast!(LValue)~ ex) {
          iparse!(Statement, "iter_array_eval_step_4", "tree.stmt")
                 (` { type-of-elem _iter temp; while temp <- _iter { var ~= temp; } }`,
                  namespace(),
                  "var", var, "_iter", lv, af).emitAsm(af);
        } else if (var) {
          iparse!(Statement, "iter_array_eval_step_5", "tree.stmt")
                 (` { auto temp = _iter; type-of-elem temp temp2; while temp2 <- temp { var ~= temp2; } }`,
                  namespace(),
                  "var", var, "_iter", ex, af).emitAsm(af);
        } else {
          iparse!(Statement, "iter_eval_step_6", "tree.stmt")
                 (` { auto temp = _iter; while temp { } }`,
                  "_iter", ex, af).emitAsm(af);
        }
      }
      if (target) {
        emitStmtInto(target);
      } else {
        if (Single!(Void) == valueType())
          emitStmtInto(null);
        else {
          static if (is(T == RichIterator)) {
            mkVar(af, valueType(), true, (Variable var) {
              // manual lvize
              mkVar(af, ex.valueType(), true, (Variable lv) {
                iparse!(Statement, "initLvVar", "tree.semicol_stmt.assign")
                       (`lvvar = ex`,
                        "lvvar", lv, "ex", ex).emitAsm(af);
                iparse!(Statement, "initVar", "tree.semicol_stmt.assign")
                       (`var = new elem[] len`,
                        "var", var, "len", iter.length(lv), "elem", iter.elemType()).emitAsm(af);
                emitStmtInto(var, lv);
              });
              af.sfree(ex.valueType().size);
            });
          } else {
            mkVar(af, new ExtArray(iter.elemType(), true), false, (Variable var) {
              emitStmtConcat(var);
            });
          }
        }
      }
    }
  }
}

Object gotIterEvalTail(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, (IType it) {
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
mixin DefaultParser!(gotIterEvalTail, "tree.rhs_partial.iter_eval", null, ".eval");

static this() {
  defineOp("length", delegate Expr(Expr ex) {
    auto iter = fastcast!(RichIterator) (ex.valueType());
    if (!iter) return null;
    return iter.length(ex);
  });
}

import tools.log;
Object gotIteratorAssign(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr target;
  if (rest(t2, "tree.expr _tree.expr.arith", &target) && t2.accept("=")) {
    Expr value;
    if (!rest(t2, "tree.expr", &value) || !gotImplicitCast(value, Single!(BogusIterator), (IType it) {
      auto ri = fastcast!(RichIterator)~ it;
      return ri && target.valueType() == new Array(ri.elemType());
    })) {
      // don't - this messes up the error of standard assignment!
      // text.setError("Mismatching types in iterator assignment: ", target, " <- ", value.valueType());
      return null;
    }
    text = t2;
    auto it = fastcast!(RichIterator)~ value.valueType();
    return new EvalIterator!(RichIterator) (value, it, target);
  } else return null;
}
mixin DefaultParser!(gotIteratorAssign, "tree.semicol_stmt.assign_iterator", "11");

Object gotElemTypeOf(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  string match = "tree.expr _tree.expr.arith";
  
  if (!rest(t2, match, &ex))
    t2.failparse("Failed to parse type-of-elem expression");
  
  if (!gotImplicitCast(ex, Single!(BogusIterator), (IType it) { return !!fastcast!(Iterator) (it); }))
    text.failparse("Expected iterator");
  
  auto it = fastcast!(Iterator) (ex.valueType());
  
  text = t2;
  return fastcast!(Object) (it.elemType());
}
mixin DefaultParser!(gotElemTypeOf, "type.of_elem", "450", "type-of-elem");
