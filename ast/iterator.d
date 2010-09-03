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
    IType elemType() { return iparse!(IType, "elem_type_range", "type")("typeof(sys.init!wrapper.cur)", "wrapper", wrapper); }
    string toString() { return Format("RangeIter(", wrapper, ")"); }
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
                    ("lv.cur + pos",
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

Object gotRangeIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr from, to;
  auto t2 = text;
  if (!cont(t2, &from)) return null;
  if (!t2.accept("..")) return null;
  if (!cont(t2, &to))
    throw new Exception("Unable to acquire second half of range def at '"~t2.next_text()~"'");
  text = t2;
  auto wrapped = new Structure(null);
  new RelMember("cur", from.valueType(), wrapped);
  new RelMember("end", to.valueType(), wrapped);
  auto range = new Range;
  range.wrapper = wrapped;
  return new RCE(range, new StructLiteral(wrapped, [from, to]));
}
mixin DefaultParser!(gotRangeIter, "tree.expr.iter_range", "11");

import ast.loops;

import tools.base: This, This_fn, rmSpace;
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
  Placeholder var;
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
    // optimize subexpr of literal
    return fold(iparse!(Expr, "foriter_get_subexpr", "tree.expr")
                       ("ex.subiter", "ex", ex));
  }
  Expr update(Expr ex, Expr newvar) {
    auto sex = ex.dup;
    void subst(ref Iterable it) {
      if (it is var) it = cast(Iterable) newvar;
      it.iterate(&subst);
    }
    sex.iterate(&subst);
    return sex;
  }
  override {
    string toString() { return Format("ForIter(", itertype, ": ", ex, ")"); }
    IType elemType() { return ex.valueType(); }
    int size() { return wrapper.size; }
    string mangle() { return "for_range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr yieldAdvance(LValue lv) {
      auto wlv = castToWrapper(lv);
      auto var = iparse!(LValue, "foriter_wlv_var_advance", "tree.expr")
                        ("wlv.var", "wlv", wlv);
      auto stmt = iparse!(Statement, "foriter_assign_advance", "tree.semicol_stmt.assign")
        ("var = ya",
         "var", var,
         "ya", itertype.yieldAdvance(subexpr(wlv))
        );
      return new StatementAndExpr(stmt, update(this.ex, var));
    }
    Cond terminateCond(Expr ex) {
      return itertype.terminateCond(subexpr(castToWrapper(ex)));
    }
    static if (is(I: RichIterator)) {
      Expr length(Expr ex) {
        return itertype.length(subexpr(castToWrapper(ex)));
      }
      Expr index(Expr ex, Expr pos) {
        auto wlv = castToWrapper(lvize(ex));
        auto var = iparse!(LValue, "foriter_wlv_var", "tree.expr")
                          ("wlv.var", "wlv", wlv);
        auto stmt = iparse!(Statement, "foriter_assign_index", "tree.semicol_stmt.assign")
                           ("var = ya",
                            "var", var,
                            "ya", itertype.index(subexpr(wlv), pos));
        return new StatementAndExpr(stmt, update(this.ex, var));
      }
      Expr slice(Expr ex, Expr from, Expr to) {
        auto wr = castToWrapper(ex);
        return new RCE(this,
          new StructLiteral(cast(Structure) wrapper, 
            [cast(Expr) new Filler(itertype.elemType()),
              itertype.slice(subexpr(wr), from, to)]));
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

class Placeholder : Expr {
  IType type;
  this(IType type) { this.type = type; }
  Placeholder dup() { return this; } // IMPORTANT.
  mixin defaultIterate!();
  IType valueType() { return type; }
  void emitAsm(AsmFile af) { assert(false); }
}

import ast.literals: DataExpr;
Object gotForIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr sub, main;
  auto t2 = text;
  if (!t2.accept("[for")) return null;
  string ivarname;
  auto t3 = t2;
  if (t3.gotIdentifier(ivarname) && t3.accept("<-")) {
    t2 = t3;
  } else ivarname = null;
  if (!rest(t2, "tree.expr", &sub, (Expr ex) { return !!cast(Iterator) ex.valueType(); }))
    throw new Exception("Cannot find sub-iterator at '"~t2.next_text()~"'! ");
  if (!t2.accept(":"))
    throw new Exception("Expected ':' at '"~t2.next_text()~"'! ");
  
  auto it = cast(Iterator) sub.valueType();
  auto ph = new Placeholder(it.elemType());
  
  Namespace backup;
  if (ivarname) {
    backup = namespace();
    auto mns = new MiniNamespace("for_iter_var");
    mns.sup = backup;
    mns.internalMode = true;
    mns.add(ivarname, ph);
    namespace.set(mns);
  }
  
  scope(exit)
    if (backup)
      namespace.set(backup);
  
  if (!rest(t2, "tree.expr", &main))
    throw new Exception("Cannot find iterator expression at '"~t2.next_text()~"'! ");
  if (!t2.accept("]"))
    throw new Exception("Expected ']' at '"~t2.next_text()~"'! ");
  text = t2;
  auto wrapped = new Structure(null);
  new RelMember("var", it.elemType(), wrapped);
  new RelMember("subiter", sub.valueType(), wrapped);
  if (auto ri = cast(RichIterator) it) {
    auto foriter = new ForIter!(RichIterator);
    foriter.wrapper = wrapped;
    foriter.itertype = ri;
    foriter.ex = main;
    foriter.var = ph;
    return new RCE(foriter, new StructLiteral(wrapped,
      [cast(Expr) new Filler(ri.elemType()), sub]));
  } else {
    auto foriter = new ForIter!(Iterator);
    foriter.wrapper = wrapped;
    foriter.itertype = it;
    foriter.ex = main;
    foriter.var = ph;
    return new RCE(foriter, new StructLiteral(wrapped,
      [cast(Expr) new Filler(it.elemType()), sub]));
  }
}
mixin DefaultParser!(gotForIter, "tree.expr.iter_for", "441");

import ast.variable, ast.assign;
class IterLetCond : Cond {
  LValue target;
  Expr iter;
  LValue iref;
  mixin MyThis!("target, iter, iref");
  mixin DefaultDup!();
  mixin defaultIterate!(iter);
  override void jumpOn(AsmFile af, bool cond, string dest) {
    auto itype = cast(Iterator) iter.valueType();
    auto step = itype.yieldAdvance(iref);
    auto itercond = itype.terminateCond(iref);
    itercond.jumpOn(af, cond, dest);
    if (target) {
      (new Assignment(target, step)).emitAsm(af);
    } else {
      step.emitAsm(af);
      af.sfree(step.valueType().size);
    }
  }
}

import ast.scopes, ast.vardecl;

// create temporary if needed
LValue lvize(Expr ex) {
  if (auto lv = cast(LValue) ex) return lv;
  
  auto sc = cast(Scope) namespace();
  if (!sc)
    throw new Exception("Can't create temporary in "~namespace().toString()~"!");
  
  auto var = new Variable(ex.valueType(), null, boffs(ex.valueType()));
  var.initval = ex;
  
  auto decl = new VarDecl;
  decl.vars ~= var;
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
  if (!rest(t2, "tree.expr", &iter, (Expr ex) { return !!cast(Iterator) ex.valueType(); }))
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
  return new IterLetCond(lv, iter, lvize(iter));
}
mixin DefaultParser!(gotIterCond, "cond.iter", "705");

Object gotIterIndex(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto iter = cast(Iterator) ex.valueType();
    if (!iter) return null;
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

import ast.arrays;
// Statement with target, Expr without. Lol.
class FlattenIterator : Expr, Statement {
  Expr ex;
  RichIterator iter;
  Expr target; // optional
  this() { }
  this(Expr ex, RichIterator ri) { this.ex = ex; this.iter = ri; }
  this(Expr ex, RichIterator ri, Expr target) { this(ex, ri); this.target = target; }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override {
    IType valueType() { return new Array(iter.elemType()); }
    void emitAsm(AsmFile af) {
      if (target) {
        iparse!(Statement, "assign_iter_to_array", "tree.stmt")
              (` { printf("Len2: %i\n", len); int i; while var[i++] <- _iter { } }`,
                  namespace(),
                  "len", iter.length(ex), "_iter", ex, "var", target, af).emitAsm(af);
      } else {
        mkVar(af, valueType(), true, (Variable var) {
          iparse!(Statement, "initVar", "tree.stmt")
                (` {
                      printf("Len: %i\n", len);
                      var = new(len) elem;
                      int i;
                      while var[i++] <- _iter { }
                    }`,
                    namespace(),
                    "len", iter.length(ex), "elem", iter.elemType(),
                    "_iter", ex, "var", var,
                    af).emitAsm(af);
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
  if (rest(t2, "tree.expr >tree.expr.arith", &target) && t2.accept("=")) {
    Expr value;
    if (!rest(t2, "tree.expr", &value, (Expr ex) {
      auto it = cast(RichIterator) ex.valueType();
      return it && target.valueType() == new Array(it.elemType());
    })) {
      error = Format("Mismatching types in iterator assignment: ", target, " <- ", value.valueType());
      logln("faiil");
      return null;
    }
    text = t2;
    auto it = cast(RichIterator) value.valueType();
    return new FlattenIterator(value, it, target);
  } else return null;
}
mixin DefaultParser!(gotIteratorAssign, "tree.semicol_stmt.assign_iterator", "11");
