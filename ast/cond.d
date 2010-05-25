module ast.cond;

import ast.base, ast.namespace, ast.parse, tools.base;

class ExprWrap : Cond {
  Expr ex;
  mixin This!("ex");
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      assert(ex.valueType().size == 4);
      ex.emitAsm(af);
      af.popStack("%eax", ex.valueType());
      af.compare("%eax", "%eax", true);
      if (cond)
        af.jumpOn(true, false, true, dest); // Jump on !=0
      else
        af.jumpOn(false, true, false, dest); // jump on 0.
    }
  }
}

class Compare : Cond {
  Expr e1; bool smaller, equal, greater; Expr e2;
  this(Expr e1, bool not, bool smaller, bool equal, bool greater, Expr e2) {
    if (not) {
      not = !not;
      smaller = !smaller;
      equal = !equal;
      greater = !greater;
    }
    this.e1 = e1;
    this.smaller = smaller; this.equal = equal; this.greater = greater;
    this.e2 = e2;
  }
  void flip() {
    swap(e1, e2);
    swap(smaller, greater);
  }
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      
      if (cast(IntExpr) e1 && !cast(IntExpr) e2)
        flip;
      
      if (auto ie = cast(IntExpr) e2) {
        e1.emitAsm(af);
        af.popStack("%eax", e1.valueType());
        // remember: at&t order is inverted
        af.compare(Format("$", ie.num), "%eax");
      } else {
        e2.emitAsm(af);
        e1.emitAsm(af);
        af.popStack("%ebx", e1.valueType());
        af.popStack("%eax", e2.valueType());
        af.compare("%eax", "%ebx");
      }
      auto s = smaller, e = equal, g = greater;
      if (!cond) { // negate
        swap(s, g);
        if (s + g == 1)
          e = !e;
      }
      af.jumpOn(s, e, g, dest);
    }
  }
}

Object gotCompare(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool not, smaller, equal, greater;
  Expr ex1, ex2;
  if (rest(t2, "tree.expr", &ex1) &&
      (
        (t2.accept("!") && (not = true)),
        (t2.accept("<") && (smaller = true)),
        (t2.accept(">") && (greater = true)),
        ((not || smaller || t2.accept("=")) && t2.accept("=") && (equal = true)),
        (smaller || equal || greater)
      ) && rest(t2, "tree.expr", &ex2)
  ) {
    text = t2;
    return new Compare(ex1, not, smaller, equal, greater, ex2);
  } else return null;
}
mixin DefaultParser!(gotCompare, "cond.compare", "1");

import ast.literals;
Object gotExprAsCond(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (rest(text, "<tree.expr >tree.expr.cond", &ex)) {
    return new ExprWrap(ex);
  } else return null;
}
mixin DefaultParser!(gotExprAsCond, "cond.expr", "8");

class BooleanOp(string Which) : Cond {
  Cond c1, c2;
  mixin This!("c1, c2");
  override {
    void jumpOn(AsmFile af, bool cond, string dest) {
      static if (Which == "&&") {
        if (cond) {
          auto past = af.genLabel();
          c1.jumpOn(af, false, past);
          c2.jumpOn(af, true, dest);
          af.emitLabel(past);
        } else {
          c1.jumpOn(af, false, dest);
          c2.jumpOn(af, false, dest);
        }
      } else
      static if (Which == "||") {
        if (cond) {
          c1.jumpOn(af, true, dest);
          c2.jumpOn(af, true, dest);
        } else {
          auto past = af.genLabel();
          c1.jumpOn(af, true, past);
          c2.jumpOn(af, false, dest);
          af.emitLabel(past);
        }
      } else
      static assert(false, "unknown boolean op: "~Which);
    }
  }
}

Object gotBoolOp(string Op)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (!cont(t2, &cd)) return null;
  auto old_cd = cd;
  while (t2.accept(Op)) {
    Cond cd2;
    if (!cont(t2, &cd2))
      throw new Exception("Couldn't get second cond after '"
        ~ Op ~ "' at '"~t2.next_text()~"'");
    cd = new BooleanOp!(Op)(cd, cd2);
  }
  if (old_cd is cd) return null;
  text = t2;
  return cast(Object) cd;
}
mixin DefaultParser!(gotBoolOp!("&&"), "cond.bool_and", "6");
mixin DefaultParser!(gotBoolOp!("||"), "cond.bool_or", "5");

Object gotBraces(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (t2.accept("(") && rest(t2, "cond", &cd) && t2.accept(")")) {
    text = t2;
    return cast(Object) cd;
  } else return null;
}
mixin DefaultParser!(gotBraces, "cond.braces", "9");
