module ast.casting;

import ast.base, ast.parse;

class ReinterpretCast(T) : T {
  T from; IType to;
  this(IType to, T from) {
    this.from = from;
    this.to = to;
    assert(to.size == from.valueType().size, Format("Can't cast ", from, " to ", to, "!"));
  }
  mixin defaultIterate!(from);
  override {
    string toString() { return Format("reinterpret_cast<", to, "> ", from); }
    IType valueType() { return to; }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("to.size"));
      from.emitAsm(af);
    }
    static if (is(typeof(&from.emitLocation)))
      void emitLocation(AsmFile af) {
        from.emitLocation(af);
      }
  }
}

Object gotCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (t2.accept("cast(")) {
    IType dest;
    if (!rest(t2, "type", &dest))
      throw new Exception("No type matched in cast expression: "~t2.next_text());
    if (!t2.accept(")"))
      throw new Exception("Missed closing bracket in cast at "~t2.next_text());
    if (!rest(t2, "tree.expr >tree.expr.arith", &ex, (Expr ex) { return ex.valueType().size == dest.size; }))
      throw new Exception("Expression not matched in cast: "~t2.next_text());
    
    text = t2;
    return new ReinterpretCast!(Expr)(dest, ex);
  } else return null;
}
mixin DefaultParser!(gotCastExpr, "tree.expr.cast", "7");

class ShortToIntCast : Expr {
  Expr sh;
  this(Expr sh) { this.sh = sh; }
  mixin defaultIterate!();
  override {
    IType valueType() { return Single!(SysInt); }
    void emitAsm(AsmFile af) {
      sh.emitAsm(af);
      af.comment("short to int cast");
      af.put("xorl %eax, %eax");
      af.popStack("%ax", sh.valueType());
      af.pushStack("%eax", valueType());
    }
  }
}

class CharToShortCast : Expr {
  Expr sh;
  this(Expr sh) { this.sh = sh; }
  mixin defaultIterate!();
  override {
    IType valueType() { return Single!(Short); }
    void emitAsm(AsmFile af) {
      sh.emitAsm(af);
      // lol.
      af.comment("byte to short cast lol");
      af.put("xorw %ax, %ax");
      af.popStack("%al", sh.valueType());
      af.pushStack("%ax", valueType());
    }
  }
}

Object gotCharToShortExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (!rest(t2, "tree.expr ^selfrule", &ex, (Expr ex) {
    return ex.valueType().size() == 1;
  }))
    return null;
  text = t2;
  return new CharToShortCast(ex);
}
mixin DefaultParser!(gotCharToShortExpr, "tree.expr.char_to_short", "951");

import tools.log;
Object gotShortToIntExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (!rest(t2, "tree.expr ^selfrule", &ex, (Expr ex) {
    return ex.valueType().size() == 2;
  }))
    return null;
  text = t2;
  return new ShortToIntCast(ex);
}
mixin DefaultParser!(gotShortToIntExpr, "tree.expr.short_to_int", "952");
