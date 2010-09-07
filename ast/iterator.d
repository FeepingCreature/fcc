module ast.iterator;

import ast.base, ast.parse, ast.types, ast.namespace, ast.structure, ast.casting;

interface Iterator {
  IType elemType();
  Expr yieldAdvance(LValue);
  Cond terminateCond(Expr); // false => can't yield more values
}

interface RichIterator : Iterator {
  Expr length(Expr);
  Expr index(Expr, Expr pos);
  Expr slice(Expr, Expr from, Expr to);
}

class Range : Type, RichIterator {
  IType wrapper;
  LValue castToWrapper(LValue lv) {
    return iparse!(LValue, "range_cast_to_wrapper", "tree.expr")
                  ("*cast(wrapper*) &lv", "lv", lv, "wrapper", wrapper);
  }
  Expr castExprToWrapper(Expr ex) {
    return iparse!(Expr, "range_cast_expr_to_wrapper", "tree.expr")
                  ("cast(wrapper) ex", "ex", ex, "wrapper", wrapper);
  }
  override {
    IType elemType() { return iparse!(IType, "elem_type_range", "type")("typeof((cast(wrapper*) 0).cur)", "wrapper", wrapper); }
    string toString() { return Format("RangeIter[", size, "](", wrapper, ")"); }
    int size() { return wrapper.size; }
    string mangle() { return "range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr yieldAdvance(LValue lv) {
      return iparse!(Expr, "yield_advance_range", "tree.expr")
                    ("lv.cur++", "lv", castToWrapper(lv));
    }
    Cond terminateCond(Expr ex) {
      return iparse!(Cond, "terminate_cond_range", "cond")
                    ("ex.cur != ex.end", "ex", castExprToWrapper(ex));
    }
    Expr length(Expr ex) {
      return iparse!(Expr, "length_range", "tree.expr")
                    ("ex.end - ex.cur", "ex", castExprToWrapper(ex));
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

import ast.loops;

import tools.base: This, This_fn, rmSpace, PTuple, Stuple, ptuple, stuple;
class StatementAndExpr : Expr {
  Statement first;
  Expr second;
  mixin MyThis!("first, second");
  mixin DefaultDup!();
  mixin defaultIterate!(first, second);
  override {
    IType valueType() { return second.valueType(); }
    void emitAsm(AsmFile af) {
      first.emitAsm(af);
      second.emitAsm(af);
    }
  }
}

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
  LValue castToWrapper(LValue lv) {
    return iparse!(LValue, "foriter_cast_to_wrapper", "tree.expr")
                  ("*cast(wrapper*) &lv", "lv", lv, "wrapper", wrapper);
  }
  Expr castToWrapper(Expr ex) {
    if (auto lv = cast(LValue) ex) return castToWrapper(lv);
    return iparse!(Expr, "foriter_cast_ex_to_wrapper", "tree.expr")
                  ("cast(wrapper) ex", "ex", ex, "wrapper", wrapper);
  }
  LValue subexpr(LValue lv) {
    return iparse!(LValue, "foriter_get_subexpr_lv", "tree.expr")
                  ("lv.subiter", "lv", lv);
  }
  Expr subexpr(Expr ex) {
    if (auto lv = cast(LValue) ex) return subexpr(lv);
    ex = opt(ex);
    // optimize subexpr of literal
    auto res = opt(iparse!(Expr, "foriter_get_subexpr", "tree.expr")
                           ("ex.subiter", "ex", ex));
    return res;
  }
  Expr update(Expr ex, Placeholder var, Expr newvar) {
    auto sex = ex.dup;
    void subst(ref Iterable it) {
      if (it is var) it = cast(Iterable) newvar;
      else it.iterate(&subst);
    }
    sex.iterate(&subst);
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
                        ("var = ya", "var", var, "ya", itertype.yieldAdvance(subexpr(wlv)));
    return stmt;
  }
  override {
    string toString() { return Format("ForIter[", size, "](", itertype, ": ", ex.valueType(), ")"); }
    IType elemType() { return ex.valueType(); }
    int size() { return wrapper.size; }
    string mangle() { return "for_range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr yieldAdvance(LValue lv) {
      LValue wlv;
      auto stmt = mkForIterAssign(lv, wlv);
      return update(new StatementAndExpr(stmt, this.ex), wlv);
    }
    Cond terminateCond(Expr ex) {
      return itertype.terminateCond(subexpr(castToWrapper(ex)));
    }
    static if (is(I: RichIterator)) {
      Expr length(Expr ex) {
        return itertype.length(subexpr(castToWrapper(ex)));
      }
      Expr index(Expr ex, Expr pos) {
        auto lv = cast(LValue) ex;
        if (!lv) throw new Exception(Format("Cannot take index of non-lvalue: ", ex));
        LValue wlv;
        auto stmt = mkForIterAssign(lv, wlv);
        return new StatementAndExpr(stmt, update(this.ex, wlv));
      }
      Expr slice(Expr ex, Expr from, Expr to) {
        auto wr = castToWrapper(ex);
        Expr[] field = [cast(Expr) itertype.slice(subexpr(wr), from, to),
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
class ScopeWithExpr : Expr {
  Scope sc;
  Expr ex;
  this(Scope sc, Expr ex) { this.sc = sc; this.ex = ex; }
  mixin defaultIterate!(sc, ex);
  override {
    ScopeWithExpr dup() { return new ScopeWithExpr(sc.dup, ex.dup); }
    IType valueType() { return ex.valueType(); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("ex.valueType().size"));
      mkVar(af, ex.valueType(), true, (Variable var) {
        sc.id = getuid();
        auto dg = sc.open(af)();
        (new Assignment(var, ex)).emitAsm(af);
        dg();
      });
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
  auto ar = cast(Array) ex.valueType(), sa = cast(StaticArray) ex.valueType();
  if (ar || sa)
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
  auto ph = new Placeholder(it.elemType(), "it.elemType()");
  
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
    throw new Exception("Cannot find iterator expression at '"~t2.next_text()~"'! ");
  if (!t2.accept("]"))
    throw new Exception("Expected ']' at '"~t2.next_text()~"'! ");
  text = t2;
  auto wrapped = new Structure(null);
  new RelMember("subiter", sub.valueType(), wrapped);
  new RelMember("var", it.elemType(), wrapped);
  if (extra)
    new RelMember("extra", extra.valueType(), wrapped);
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
  ipt = stuple(wrapped, new ScopeWithExpr(sc, main), ph, extra);
  Expr[] field;
  if (extra) field = [cast(Expr) sub, new Filler(it.elemType()), exEx];
  else field = [cast(Expr) sub, new Filler(it.elemType())];
  return new RCE(cast(IType) restype, new StructLiteral(wrapped, field));
}
mixin DefaultParser!(gotForIter, "tree.expr.iter.for");
static this() {
  parsecon.addPrecedence("tree.expr.iter", "441");
}

import ast.variable, ast.assign;
class IterLetCond : Cond, NeedsConfig {
  LValue target;
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
      (new Assignment(target, step)).emitAsm(af);
    } else {
      logln("emit step for ", itype);
      step.emitAsm(af);
      af.sfree(step.valueType().size);
    }
  }
  override string toString() {
    if (target) return Format(target, " <- ", iter);
    else return Format("eval ", iter);
  }
}

import ast.scopes, ast.vardecl;

// create temporary if needed
LValue lvize(Expr ex) {
  if (auto lv = cast(LValue) ex) return lv;
  
  auto var = new Variable(ex.valueType(), "__lol", boffs(ex.valueType()));
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
  Variable newvar;
  bool needIterator;
  if (!rest(t2, "tree.expr", &lv)) {
    IType ty; string name;
    if (!rest(t2, "type", &ty) || !t2.gotIdentifier(name))
      goto withoutIterator;
    newvar = new Variable(ty, name, boffs(ty));
    newvar.initInit();
    lv = newvar;
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
  if (!sc) throw new Exception("Bad place for an iter cond: "~Format(namespace())~"!");
  
  if (newvar) {
    auto decl = new VarDecl;
    decl.vars ~= newvar;
    sc.addStatement(decl);
    sc.add(newvar);
  }
  return new IterLetCond(lv, iter, iter);
}
mixin DefaultParser!(gotIterCond, "cond.iter", "705");

Object gotIterEval(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue lv;
  if (!t2.accept("eval")) return null;
  if (!rest(t2, "tree.expr", &lv)) return null;
  auto it = cast(Iterator) lv.valueType();
  if (!it) return null;
  text = t2;
  return cast(Object) it.yieldAdvance(lv);
}
mixin DefaultParser!(gotIterEval, "tree.expr.eval_iter", "270");

Object gotIterIndex(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto iter = cast(Iterator) ex.valueType();
    if (!iter) return null;
    // if (!cast(LValue) ex) return null;
    auto t2 = text;
    Expr pos;
    if (t2.accept("[") && rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      text = t2;
      auto ri = cast(RichIterator) iter;
      if (!ri)
        throw new Exception(Format("Cannot access by index ",
          ex, " at ", text.next_text(), ": not a rich iterator! "));
      
      if (auto range = cast(Range) pos.valueType()) {
        auto ps = new RCE(range.wrapper, pos);
        auto from = iparse!(Expr, "iter_slice_from", "tree.expr")
                           ("ps.cur", "ps", ps);
        auto to   = iparse!(Expr, "iter_slice_to",   "tree.expr")
                           ("ps.end", "ps", ps);
        return cast(Object) ri.slice(ex, from, to);
      } else {
        return cast(Object) ri.index(ex, pos);
      }
    } else return null;
  };
}
mixin DefaultParser!(gotIterIndex, "tree.rhs_partial.iter_index");

import ast.arrays, ast.modules, ast.aggregate;
// Statement with target, Expr without. Lol.
class FlattenIterator : Expr, Statement {
  Expr ex;
  RichIterator iter;
  Expr target; // optional
  private this() { }
  this(Expr ex, RichIterator ri) {
    this.ex = ex;
    this.iter = ri;
  }
  this(Expr ex, RichIterator ri, Expr target) {
    this(ex, ri);
    this.target = target;
  }
  FlattenIterator dup() {
    auto res = new FlattenIterator;
    res.ex = ex.dup;
    res.iter = iter;
    res.target = target;
    return res;
  }
  mixin defaultIterate!(ex, target);
  override {
    IType valueType() { return new Array(iter.elemType()); }
    string toString() { return Format("flatten(", ex, ")"); }
    void emitAsm(AsmFile af) {
      int offs;
      void emitStmt(Expr var) {
        if (auto lv = cast(LValue) ex) {
          iparse!(Statement, "iter_array_flatten_step_1", "tree.stmt")
                 (` { int i; while var[i++] <- _iter { } }`,
                  "var", var, "_iter", lv, af).emitAsm(af);
        } else {
          iparse!(Statement, "iter_array_flatten_step_2", "tree.stmt")
                 (` { int i; auto temp = _iter; while var[i++] <- temp { } }`,
                  "var", var, "_iter", ex, af).emitAsm(af);
        }
      }
      if (target) {
        emitStmt(target);
      } else {
        mkVar(af, valueType(), true, (Variable var) {
          iparse!(Statement, "initVar", "tree.semicol_stmt.assign")
                (`var = new(len) elem`,
                 "var", var, "len", iter.length(ex), "elem", iter.elemType()).emitAsm(af);
          emitStmt(var);
        });
      }
    }
  }
}

Object gotIterFlatten(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto iter = cast(RichIterator) ex.valueType();
    if (!iter) return null;
    if (!text.accept(".flatten")) return null;
    return new FlattenIterator(ex, iter);
  };
}
mixin DefaultParser!(gotIterFlatten, "tree.rhs_partial.iter_flatten");

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
    return new FlattenIterator(value, it, target);
  } else return null;
}
mixin DefaultParser!(gotIteratorAssign, "tree.semicol_stmt.assign_iterator", "11");
