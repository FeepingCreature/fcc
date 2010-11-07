module ast.iterator;

import ast.base, ast.parse, ast.types, ast.namespace, ast.structure, ast.casting;

interface Iterator {
  IType elemType();
  Expr yieldAdvance(LValue);
  Cond terminateCond(Expr); // false => can't yield more values
}

interface RichIterator : Iterator {
  Expr length(Expr);
  Expr index(LValue, Expr pos);
  Expr slice(Expr, Expr from, Expr to);
}

class Range : Type, RichIterator {
  IType wrapper;
  LValue castToWrapper(LValue lv) {
    return iparse!(LValue, "range_cast_to_wrapper", "tree.expr")
                  ("*wrapper*:&lv", "lv", lv, "wrapper", wrapper);
  }
  Expr castExprToWrapper(Expr ex) {
    return iparse!(Expr, "range_cast_expr_to_wrapper", "tree.expr")
                  ("wrapper:ex", "ex", ex, "wrapper", wrapper);
  }
  override {
    IType elemType() { return iparse!(IType, "elem_type_range", "type")("typeof((wrapper*:null).cur)", "wrapper", wrapper); }
    string toString() { return Format("RangeIter[", size, "](", wrapper, ")"); }
    int size() { return wrapper.size; }
    string mangle() { return "range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr yieldAdvance(LValue lv) {
      return iparse!(Expr, "yield_advance_range", "tree.expr")
                    ("lv.cur++", "lv", castToWrapper(lv));
    }
    import ast.conditionals: Compare;
    Cond terminateCond(Expr ex) {
      ex = castExprToWrapper(ex);
      return new Compare(
        mkMemberAccess(ex, "cur"),
        "!=",
        mkMemberAccess(ex, "end")
      );
    }
    Expr length(Expr ex) {
      return iparse!(Expr, "length_range", "tree.expr")
                    ("ex.end - ex.cur", "ex", castExprToWrapper(ex));
    }
    Expr index(LValue lv, Expr pos) {
      return iparse!(Expr, "index_range", "tree.expr")
                    ("lv.cur + pos",
                     "lv", castExprToWrapper(lv),
                     "pos", pos);
    }
    Expr slice(Expr ex, Expr from, Expr to) {
      return iparse!(Expr, "slice_range", "tree.expr")
                    ("(ex.cur + from) .. (ex.cur + to)",
                     "ex", castExprToWrapper(ex),
                     "from", from, "to", to);
    }
  }
}

import ast.tuples;
Object gotRangeIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr from, to;
  auto t2 = text;
  if (!cont(t2, &from)) return null;
  if (!t2.accept("..")) return null;
  if (!cont(t2, &to))
    throw new Exception("Unable to acquire second half of range def at '"~t2.next_text()~"'");
  text = t2;
  bool notATuple(IType it) { return !cast(Tuple) it; }
  gotImplicitCast(from, &notATuple);
  gotImplicitCast(to  , &notATuple);
  auto wrapped = new Structure(null);
  new RelMember("cur", from.valueType(), wrapped);
  new RelMember("end", to.valueType(), wrapped);
  auto range = new Range;
  range.wrapper = wrapped;
  return new RCE(range, new StructLiteral(wrapped, [from, to]));
}
mixin DefaultParser!(gotRangeIter, "tree.expr.iter_range", "11");

class StructIterator : Type, Iterator {
  IType wrapped;
  IType _elemType;
  this(IType it) {
    wrapped = it;
    _elemType = iparse!(Expr, "si_elemtype", "tree.expr")
                       (`eval (bogus.step)`,
                        "bogus", new Placeholder(wrapped, "si_elemtype_ph")
                       ).valueType();
  }
  override {
    int size() { return wrapped.size; }
    string mangle() { return "struct_iterator_"~wrapped.mangle(); }
    ubyte[] initval() { return wrapped.initval; }
    IType elemType() { return _elemType; }
    Expr yieldAdvance(LValue lv) {
      return iparse!(Expr, "si_step", "tree.expr")
                    (`eval (lv.step)`,
                     "lv", lv, "W", wrapped);
    }
    Cond terminateCond(Expr ex) {
      return iparse!(Cond, "si_ivalid", "cond")
                    (`eval (ex.ivalid)`,
                     "ex", ex, "W", wrapped);
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (auto si = cast(StructIterator) ex.valueType()) {
      return reinterpret_cast(si.wrapped, ex);
    }
    return null;
  };
}

import ast.templ;
Object gotStructIterator(ref string text, ParseCb cont, ParseCb rest) {
  if (text == ".step)" || text == ".ivalid)")
    return null; // prevent the tests below from looping. HAX.
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    Expr iter;
    if (auto templ = cast(Template) obj) {
      Expr nex;
      if (!rest(t2, "tree.expr", &nex)) return null;
      iter = iparse!(Expr, "si_call_test", "tree.expr")
                         (`templ!typeof(nex)(nex)`,
                          namespace(),
                          "templ", templ, "nex", nex);
      if (!iter) {
        logln("no template :(");
        
        return null;
      }
    } else {
      // logln("else ", obj);
      // asm { int 3; }
      return null;
    }
    // logln("try ", t2.next_text(), "; ", iter);
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

Object gotIterIvalid(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("__ivalid")) return null;
  Expr ex;
  IType[] tried;
  if (!rest(t2, "tree.expr", &ex) || !gotImplicitCast(ex, (IType it) { return !!cast(Iterator) it; }))
    throw new Exception(Format("Couldn't find iter expr for eoi at '", text.next_text(), "'; tried ", tried, ". "));
  auto it = cast(Iterator) ex.valueType();
  text = t2;
  return cast(Object) it.terminateCond(ex);
}
mixin DefaultParser!(gotIterIvalid, "cond.ivalid", "76");

import ast.loops;

import tools.base: This, This_fn, rmSpace, PTuple, Stuple, ptuple, stuple;

class StatementAndCond : Cond {
  Statement first;
  Cond second;
  mixin MyThis!("first, second");
  mixin DefaultDup!();
  mixin defaultIterate!(first, second);
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      first.emitAsm(af);
      second.jumpOn(af, cond, dest);
    }
  }
}

import ast.fold;
class ForIter(I) : Type, I {
  IType wrapper;
  I itertype;
  Expr ex;
  Placeholder var, extra;
  ForIter dup() {
    auto res = new ForIter;
    res.wrapper = wrapper;
    res.itertype = itertype;
    res.ex = ex.dup;
    res.var = var; res.extra = extra;
    return res;
  }
  LValue castToWrapper(LValue lv) {
    return iparse!(LValue, "foriter_cast_to_wrapper", "tree.expr")
                  ("*wrapper*:&lv", "lv", lv, "wrapper", wrapper);
  }
  Expr castToWrapper(Expr ex) {
    if (auto lv = cast(LValue) ex) return castToWrapper(lv);
    return iparse!(Expr, "foriter_cast_ex_to_wrapper", "tree.expr")
                  ("wrapper:ex", "ex", ex, "wrapper", wrapper);
  }
  LValue subexpr(LValue lv) {
    return iparse!(LValue, "foriter_get_subexpr_lv", "tree.expr")
                  ("lv.subiter", "lv", lv);
  }
  Expr subexpr(Expr ex) {
    if (auto lv = cast(LValue) ex) return subexpr(lv);
    opt(ex);
    // optimize subexpr of literal
    auto res = iparse!(Expr, "foriter_get_subexpr", "tree.expr")
                      ("ex.subiter", "ex", ex);
    opt(res);
    return res;
  }
  import ast.literal_string;
  Expr update(Expr ex, Placeholder var, Expr newvar) {
    Expr[] todo;
    void subst(ref Iterable it) {
      if (it is var) it = cast(Iterable) newvar;
      else {
        auto ex = cast(Expr) it;
        if (ex) {
          if (auto fi = cast(ForIter!(RichIterator)) ex.valueType()) {
            auto fi2 = fi.dup;
            todo ~= fi2.ex;
            it = cast(Iterable) reinterpret_cast(fi2, ex);
            (cast(Iterable) ex).iterate(&subst);
            return;
          } else if (auto fi = cast(ForIter!(Iterator)) ex.valueType()) {
            auto fi2 = fi.dup;
            todo ~= fi2.ex;
            it = cast(Iterable) reinterpret_cast(fi2, ex);
            (cast(Iterable) ex).iterate(&subst);
            return;
          }
        }
        it.iterate(&subst);
      }
    }
    auto sex = ex.dup;
    todo ~= sex;
    bool[Expr] done;
    while (todo.length) {
      auto cur_ex = todo.take();
      if (cur_ex in done) continue;
      done[cur_ex] = true;
      cur_ex.iterate(&subst);
    }
    return sex;
  }
  Expr update(Expr ex, LValue lv) {
    auto var = iparse!(LValue, "foriter_lv_var_lookup", "tree.expr")
                      ("lv.var", "lv", lv);
    ex = update(ex, this.var, var);
    if (this.extra) {
      auto extra = iparse!(LValue, "foriter_lv_extra_lookup", "tree.expr")
                      ("lv.extra", "lv", lv);
      ex = update(ex, this.extra, extra);
    }
    return ex;
  }
  Statement mkForIterAssign(LValue lv, ref LValue wlv) {
    wlv = castToWrapper(lv);
    auto var = iparse!(LValue, "foriter_wlv_var", "tree.expr")
                      ("wlv.var", "wlv", wlv);
    auto stmt = iparse!(Statement, "foriter_assign", "tree.semicol_stmt.assign")
                        ("var = ya", "var", var, "ya", itertype.yieldAdvance(subexpr(wlv.dup)));
    return stmt;
  }
  override {
    string toString() {
      auto sizeinfo = Format(size, ":");
      foreach (type; (cast(Structure) wrapper).types) sizeinfo ~= Format(" ", type.size);
      return Format("ForIter[", sizeinfo, "](", itertype, ": ", ex.valueType(), ")");
    }
    IType elemType() { return ex.valueType(); }
    int size() { return wrapper.size; }
    string mangle() { return "for_range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr yieldAdvance(LValue lv) {
      LValue wlv;
      auto stmt = mkForIterAssign(lv, wlv);
      // logln("!! this.ex is ", this.ex);
      return update(new StatementAndExpr(stmt, this.ex.dup), wlv);
    }
    Cond terminateCond(Expr ex) {
      return itertype.terminateCond(subexpr(castToWrapper(ex).dup));
    }
    static if (is(I: RichIterator)) {
      Expr length(Expr ex) {
        return itertype.length(subexpr(castToWrapper(ex).dup));
      }
      Expr index(LValue lv, Expr pos) {
        auto wlv = castToWrapper(lv);
        auto stmt = iparse!(Statement, "foriter_assign", "tree.semicol_stmt.assign")
                            ("wlv.var = id", "wlv", wlv, "id", itertype.index(subexpr(wlv.dup), pos));
        return new StatementAndExpr(stmt, update(this.ex.dup, wlv));
      }
      Expr slice(Expr ex, Expr from, Expr to) {
        auto wr = castToWrapper(ex);
        Expr[] field = [cast(Expr) itertype.slice(subexpr(wr.dup), from, to),
                        new Filler(itertype.elemType())];
        if (extra) field ~= extra;
        return new RCE(this,
          new StructLiteral(cast(Structure) wrapper, field));
      }
    }
  }
}

class Filler : Expr {
  IType type;
  this(IType type) { this.type = type; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { af.salloc(type.size); }
  }
}

class Placeholder : LValue {
  IType type;
  string info;
  this(IType type, string info) { this.type = type; this.info = info; }
  Placeholder dup() { return this; } // IMPORTANT.
  mixin defaultIterate!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { logln("DIAF ", info); asm { int 3; } assert(false); }
    void emitLocation(AsmFile af) { assert(false); }
    string toString() { return Format("Placeholder(", info, ")"); }
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
      sc.id = getuid();
      if (ex.valueType() == Single!(Void)) {
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
}

import ast.static_arrays;
class Tagged : Expr {
  Expr ex;
  string tag;
  this(Expr ex, string tag) { this.ex = ex; this.tag = tag; }
  mixin defaultIterate!(ex);
  override {
    Tagged dup() { return new Tagged(ex.dup, tag); }
    IType valueType() { return ex.valueType(); }
    void emitAsm(AsmFile af) { ex.emitAsm(af); }
  }
}

bool forb(ref Expr ex) {
  auto ar = cast(Array) ex.valueType(), sa = cast(StaticArray) ex.valueType(), ea = cast(ExtArray) ex.valueType();
  if (ar || sa || ea)
    ex = new Tagged(ex, "want-iterator");
  return true;
}

import ast.aggregate, ast.literals: DataExpr;
Object gotForIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr sub, main;
  auto t2 = text;
  if (!t2.accept("[for")) return null;
  string ivarname;
  auto t3 = t2;
  if (t3.gotIdentifier(ivarname) && t3.accept("<-")) {
    t2 = t3;
  } else ivarname = null;
  if (!rest(t2, "tree.expr", &sub) || !forb(sub) || !gotImplicitCast(sub, (IType it) { return !!cast(Iterator) it; }))
    throw new Exception("Cannot find sub-iterator at '"~t2.next_text()~"'! ");
  Placeholder extra;
  Expr exEx, exBind;
  if (t2.accept("extra")) {
    if (!rest(t2, "tree.expr", &exEx))
      throw new Exception("Couldn't match extra at '"~t2.next_text()~"'. ");
    extra = new Placeholder(exEx.valueType(), "exEx.valueType()");
    if (auto dc = cast(DontCastMeExpr) exEx)
      exBind = new DontCastMeExpr(extra); // propagate outwards
    else
      exBind = extra;
  }
  if (!t2.accept(":"))
    throw new Exception("Expected ':' at '"~t2.next_text()~"'! ");
  
  auto it = cast(Iterator) sub.valueType();
  auto ph = new Placeholder(it.elemType(), "it.elemType() "~ivarname);
  
  auto backup = namespace();
  auto mns = new MiniNamespace("for_iter_var");
  with (mns) {
    sup = backup;
    internalMode = true;
    if (ivarname) add(ivarname, ph);
    if (extra)    add("extra", exBind);
  }
  namespace.set(mns);
  scope(exit) namespace.set(backup);
  
  auto sc = new Scope;
  namespace.set(sc);
  
  if (!rest(t2, "tree.expr", &main))
    throw new Exception("Cannot find iterator expression at '"~t2.next_text()~"' in '"~text.next_text(32)~"'! ");
  if (!t2.accept("]"))
    throw new Exception("Expected ']' at '"~t2.next_text()~"'; partial is "~Format(main.valueType())~". ");
  text = t2;
  Expr res;
  PTuple!(IType, Expr, Placeholder, Placeholder) ipt;
  Iterator restype;
  if (auto ri = cast(RichIterator) it) {
    auto foriter = new ForIter!(RichIterator);
    with (foriter) ipt = ptuple(wrapper, ex, var, extra);
    foriter.itertype = ri;
    restype = foriter;
  } else {
    auto foriter = new ForIter!(Iterator);
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
  return new RCE(cast(IType) restype, new StructLiteral(best, field));
}
mixin DefaultParser!(gotForIter, "tree.expr.iter.for");
static this() {
  parsecon.addPrecedence("tree.expr.iter", "441");
}

import ast.variable, ast.assign;
class IterLetCond(T) : Cond, NeedsConfig {
  T target;
  Expr iter;
  LValue iref;
  Expr iref_pre;
  mixin MyThis!("target, iter, iref_pre");
  mixin DefaultDup!();
  mixin defaultIterate!(iter, target, iref);
  override void configure() { iref = lvize(iref_pre); }
  override void jumpOn(AsmFile af, bool cond, string dest) {
    auto itype = cast(Iterator) iter.valueType();
    auto step = itype.yieldAdvance(iref);
    auto itercond = itype.terminateCond(iref);
    assert(!cond); // must jump only on _fail_.
    itercond.jumpOn(af, cond, dest);
    if (target) {
      static if (is(T: MValue))
        (new _Assignment!(MValue) (target, step)).emitAsm(af);
      else (new Assignment(target, step)).emitAsm(af);
    } else {
      step.emitAsm(af);
      if (step.valueType() != Single!(Void))
        af.sfree(step.valueType().size);
    }
  }
  override string toString() {
    if (target) return Format(target, " <- ", iter);
    else return Format("test ", iter);
  }
}

import ast.scopes, ast.vardecl;

// create temporary if needed
LValue lvize(Expr ex) {
  if (auto lv = cast(LValue) ex) return lv;
  
  auto var = new Variable(ex.valueType(), null, boffs(ex.valueType()));
  auto sc = cast(Scope) namespace();
  assert(!!sc);
  var.initval = ex;
  
  auto decl = new VarDecl;
  decl.vars ~= var;
  var.baseOffset = -sc.framesize - ex.valueType().size;
  sc.addStatement(decl);
  sc.add(var);
  return var;
}

Object gotIterCond(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue lv;
  MValue mv;
  string newVarName; IType newVarType;
  bool needIterator;
  if (!rest(t2, "tree.expr", &lv, (LValue lv) { return !cast(Iterator) lv.valueType(); })) {
    if (!rest(t2, "tree.expr", &mv, (MValue mv) { return !cast(Iterator) mv.valueType(); })) {
      if (!t2.accept("auto") && !rest(t2, "type", &newVarType) || !t2.gotIdentifier(newVarName))
        goto withoutIterator;
    }
  }
  if (!t2.accept("<-"))
    return null;
  needIterator = true;
withoutIterator:
  Expr iter;
  if (!rest(t2, "tree.expr", &iter) || !forb(iter) || !gotImplicitCast(iter, (IType it) { return !!cast(Iterator) it; }))
    if (needIterator) throw new Exception("Can't find iterator at '"~t2.next_text()~"'! ");
    else return null;
  text = t2;
  // insert declaration into current scope.
  // NOTE: this here is the reason why everything that tests a cond has to have its own scope.
  auto sc = cast(Scope) namespace();
  // if (!sc) throw new Exception("Bad place for an iter cond: "~Format(namespace())~"!");
  if (!sc) return null;
  
  if (newVarName) {
    if (!newVarType) newVarType = (cast(Iterator) iter.valueType()).elemType();
    auto newvar = new Variable(newVarType, newVarName, boffs(newVarType));
    newvar.initInit();
    lv = newvar;
    auto decl = new VarDecl;
    decl.vars ~= newvar;
    sc.addStatement(decl);
    sc.add(newvar);
  }
  if (lv) return new IterLetCond!(LValue) (lv, iter, iter);
  else return new IterLetCond!(MValue) (mv, iter, iter);
}
mixin DefaultParser!(gotIterCond, "cond.iter", "705");

Object gotIterEval(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("__istep")) return null;
  Object obj;
  if (!rest(t2, "tree.expr", &obj) || !cast(LValue) obj) {
    logln("refusing istep - nothing matched or not lvalue: ", obj);
    return null;
  }
  auto lv = cast(LValue) obj;
  auto it = cast(Iterator) lv.valueType();
  if (!it) {
    logln("refusing istep: not an iterator ", lv.valueType());
    return null;
  }
  text = t2;
  return cast(Object) it.yieldAdvance(lv);
}
mixin DefaultParser!(gotIterEval, "tree.expr.eval_iter", "270");

class TempIndex : Expr {
  RichIterator ri; Expr ex, pos;
  this(RichIterator ri, Expr ex, Expr pos) {
    this.ri = ri;
    this.ex = ex;
    this.pos = pos;
  }
  mixin defaultIterate!(ex, pos);
  override {
    TempIndex dup() { return new TempIndex(ri, ex.dup, pos.dup); }
    IType valueType() { return ri.elemType(); }
    import ast.vardecl, ast.assign;
    void emitAsm(AsmFile af) {
      mkVar(af, valueType(), true, (Variable var) {
        auto v2 = new Variable(ex.valueType(), null, boffs(ex.valueType(), af.currentStackDepth));
        ex.emitAsm(af);
        (new Assignment(var, ri.index(v2, pos))).emitAsm(af);
        af.sfree(ex.valueType().size);
      });
    }
  }
}


Object gotIterIndex(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto iter = cast(Iterator) ex.valueType();
    if (!iter) return null;
    auto t2 = text;
    Expr pos;
    if (t2.accept("[") && rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      auto ri = cast(RichIterator) iter;
      if (!ri)
        throw new Exception(Format("Cannot access by index ",
          ex, " at ", text.next_text(), ": not a rich iterator! "));
      text = t2;
      if (auto range = cast(Range) pos.valueType()) {
        auto ps = new RCE(range.wrapper, pos);
        auto from = iparse!(Expr, "iter_slice_from", "tree.expr")
                           ("ps.cur", "ps", ps);
        auto to   = iparse!(Expr, "iter_slice_to",   "tree.expr")
                           ("ps.end", "ps", ps);
        return cast(Object) ri.slice(ex, from, to);
      } else {
        auto lv = cast(LValue) ex;
        if (!lv) {
          return new TempIndex(ri, ex, pos);
        }
        return cast(Object) ri.index(lv, pos);
      }
    } else return null;
  };
}
mixin DefaultParser!(gotIterIndex, "tree.rhs_partial.iter_index");

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
      if (iter.elemType() == Single!(Void))
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
      void emitStmtInto(Expr var) {
        if (auto lv = cast(LValue) ex) {
          iparse!(Statement, "iter_array_eval_step_1", "tree.stmt")
                 (` { int i; while var[i++] <- _iter { } }`,
                  "var", var, "_iter", lv, af).emitAsm(af);
        } else if (var) {
          iparse!(Statement, "iter_array_eval_step_2", "tree.stmt")
                 (` { int i; auto temp = _iter; while var[i++] <- temp { } }`,
                  "var", var, "_iter", ex, af).emitAsm(af);
        } else {
          iparse!(Statement, "iter_eval_step_3", "tree.stmt")
                 (` { auto temp = _iter; while temp { } }`,
                  "_iter", ex, af).emitAsm(af);
        }
      }
      void emitStmtConcat(Expr var) {
        if (auto lv = cast(LValue) ex) {
          iparse!(Statement, "iter_array_eval_step_4", "tree.stmt")
                 (` { typeof(__istep _iter) temp; while temp <- _iter { var ~= temp; } }`,
                  namespace(),
                  "var", var, "_iter", lv, af).emitAsm(af);
        } else if (var) {
          iparse!(Statement, "iter_array_eval_step_5", "tree.stmt")
                 (` { auto temp = _iter; typeof(__istep temp) temp2; while temp2 <- temp { var ~= temp2; } }`,
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
        if (valueType() == Single!(Void))
          emitStmtInto(null);
        else {
          static if (is(T == RichIterator)) {
            mkVar(af, valueType(), true, (Variable var) {
              iparse!(Statement, "initVar", "tree.semicol_stmt.assign")
                    (`var = new elem[len]`,
                    "var", var, "len", iter.length(ex), "elem", iter.elemType()).emitAsm(af);
              emitStmtInto(var);
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
    auto t2 = text;
    if (!t2.accept(".eval")) return null;
    auto iter = cast(Iterator) ex.valueType();
    if (!iter) return null;
    text = t2;
    if (auto ri = cast(RichIterator) iter) {
      return new EvalIterator!(RichIterator) (ex, ri);
    } else {
      return new EvalIterator!(Iterator) (ex, iter);
    }
  };
}
mixin DefaultParser!(gotIterEvalTail, "tree.rhs_partial.iter_eval");

Object gotIterLength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto iter = cast(RichIterator) ex.valueType();
    if (!iter) return null;
    if (!text.accept(".length")) return null;
    return cast(Object) iter.length(ex);
  };
}
mixin DefaultParser!(gotIterLength, "tree.rhs_partial.iter_length");

import tools.log;
Object gotIteratorAssign(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr target;
  if (rest(t2, "tree.expr _tree.expr.arith", &target) && t2.accept("=")) {
    Expr value;
    if (!rest(t2, "tree.expr", &value) || !forb(value) || !gotImplicitCast(value, (IType it) {
      auto ri = cast(RichIterator) it;
      return ri && target.valueType() == new Array(ri.elemType());
    })) {
      error = Format("Mismatching types in iterator assignment: ", target, " <- ", value.valueType());
      return null;
    }
    text = t2;
    auto it = cast(RichIterator) value.valueType();
    return new EvalIterator!(RichIterator) (value, it, target);
  } else return null;
}
mixin DefaultParser!(gotIteratorAssign, "tree.semicol_stmt.assign_iterator", "11");
