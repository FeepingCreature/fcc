module ast.iterator;

import ast.base, ast.parse, ast.types, ast.namespace, ast.structure, ast.casting;

interface Iterator {
  IType elemType();
  Expr yieldAdvance(LValue);
  Cond terminateCond(LValue); // false => can't yield more values
}

class Range : Type, Iterator {
  IType wrapper;
  Expr castToWrapper(LValue lv) {
    return iparse!(Expr, "range_cast_to_wrapper", "tree.expr")("*cast(wrapper*) &lv", "lv", lv, "wrapper", wrapper);
  }
  override {
    IType elemType() { return iparse!(IType, "elem_type_range", "type")("typeof(sys.init!wrapper.cur)", "wrapper", wrapper); }
    string toString() { return Format("RangeIter(", wrapper, ")"); }
    int size() { return wrapper.size; }
    string mangle() { return "range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr yieldAdvance(LValue lv) {
      return iparse!(Expr, "yield_advance_range", "tree.expr")("ex.cur++", "ex", castToWrapper(lv));
    }
    Cond terminateCond(LValue lv) {
      return iparse!(Cond, "terminate_cond_range", "cond")("ex.cur != ex.end", "ex", castToWrapper(lv));
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
mixin DefaultParser!(gotRangeIter, "tree.expr.iter.range");

static this() { parsecon.addPrecedence("tree.expr.iter", "11"); }

// auto iter = [for 0..256: 5] for x <- iter { }
// ==
// for x <- 0..256 { }

import ast.loops;

import tools.base: This, This_fn, rmSpace;
class StatementAndExpr : Expr {
  Statement first;
  Expr second;
  mixin This!("first, second");
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
  mixin This!("first, second");
  mixin defaultIterate!(first, second);
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      first.emitAsm(af);
      second.jumpOn(af, cond, dest);
    }
  }
}

class ForIter : Type, Iterator {
  IType wrapper;
  Iterator itertype;
  Expr ex;
  LValue castToWrapper(LValue lv) {
    return iparse!(LValue, "foriter_cast_to_wrapper", "tree.expr")("*cast(wrapper*) &lv", "lv", lv, "wrapper", wrapper);
  }
  LValue subexpr(LValue lv) {
    return iparse!(LValue, "foriter_get_subexpr", "tree.expr")("lv.subiter", "lv", lv);
  }
  override {
    string toString() { return Format("ForIter(", itertype, ": ", ex, ")"); }
    IType elemType() { return ex.valueType(); }
    int size() { return wrapper.size; }
    string mangle() { return "for_range_over_"~wrapper.mangle(); }
    ubyte[] initval() { return wrapper.initval(); }
    Expr yieldAdvance(LValue lv) {
      auto wlv = castToWrapper(lv);
      auto stmt = iparse!(Statement, "foriter_assign_advance", "tree.semicol_stmt.assign")
        ("wlv.var = ya",
        "wlv", wlv,
        "ya", itertype.yieldAdvance(subexpr(wlv))
        );
      return new StatementAndExpr(stmt, this.ex);
    }
    Cond terminateCond(LValue lv) {
      return itertype.terminateCond(subexpr(castToWrapper(lv)));
    }
  }
}

class Filler : Expr {
  IType type;
  this(IType type) { this.type = type; }
  mixin defaultIterate!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { af.salloc(type.size); }
  }
}

import ast.literals: DataExpr;
Object gotForIter(ref string text, ParseCb cont, ParseCb rest) {
  Expr sub, main;
  auto t2 = text;
  if (!t2.accept("[for")) return null;
  // TODO: allow iteration variable
  if (!rest(t2, "tree.expr", &sub, (Expr ex) { return !!cast(Iterator) ex.valueType(); }))
    throw new Exception("Cannot find sub-iterator at '"~t2.next_text()~"'! ");
  if (!t2.accept(":"))
    throw new Exception("Expected ':' at '"~t2.next_text()~"'! ");
  if (!rest(t2, "tree.expr", &main))
    throw new Exception("Cannot find iterator expression at '"~t2.next_text()~"'! ");
  if (!t2.accept("]"))
    throw new Exception("Expected ']' at '"~t2.next_text()~"'! ");
  text = t2;
  auto wrapped = new Structure(null);
  new RelMember("var", (cast(Iterator) sub.valueType()).elemType(), wrapped);
  new RelMember("subiter", sub.valueType(), wrapped);
  auto foriter = new ForIter;
  foriter.wrapper = wrapped;
  foriter.itertype = cast(Iterator) sub.valueType();
  foriter.ex = main;
  return new RCE(foriter, new StructLiteral(wrapped, [cast(Expr) new Filler(foriter.itertype.elemType()), sub]));
}
mixin DefaultParser!(gotForIter, "tree.expr.iter.for");

import ast.variable, ast.assign;
class IterLetCond : Cond {
  LValue target;
  Expr iter;
  Variable ivar;
  mixin This!("target, iter, ivar");
  mixin defaultIterate!(iter);
  override void jumpOn(AsmFile af, bool cond, string dest) {
    auto itype = cast(Iterator) iter.valueType();
    auto step = itype.yieldAdvance(ivar);
    auto itercond = itype.terminateCond(ivar);
    itercond.jumpOn(af, cond, dest);
    if (target) (new Assignment(target, step)).emitAsm(af);
    else {
      step.emitAsm(af);
      af.sfree(step.valueType().size);
    }
  }
}

import ast.scopes, ast.vardecl;
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
    if (!t2.accept("<-"))
      return null;
    needIterator = true;
  }
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
  
  auto ivar = new Variable(iter.valueType(), null, boffs(iter.valueType()));
  ivar.initval = iter;
  {
    auto decl = new VarDecl;
    decl.vars ~= ivar;
    sc.addStatement(decl);
    sc.add(ivar);
  }
  return new IterLetCond(lv, iter, ivar);
}
mixin DefaultParser!(gotIterCond, "cond.iter", "705");
