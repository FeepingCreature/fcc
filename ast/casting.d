module ast.casting;

import ast.base, ast.parse;

class ReinterpretCast(T) : T {
  T from; IType to;
  this(IType to, T from) {
    this.from = from;
    this.to = to;
    assert(to.size == from.valueType().size, Format("Can't cast ", from, " to ", to, "; ", from.valueType().size, " vs. ", to.size, "!"));
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
alias ReinterpretCast!(Expr) RCE;

// casts to types that'd be implicit-converted anyway
Object gotExplicitDefaultCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!t2.accept("cast(")) return null;
  IType dest;
  if (!rest(t2, "type", &dest))
    throw new Exception("No type matched in cast expression: "~t2.next_text());
  if (!t2.accept(")"))
    throw new Exception("Missed closing bracket in cast at "~t2.next_text());
  char* longest;
  Expr match;
  if (!rest(t2, "tree.expr >tree.expr.arith", &ex, (Expr ex) {
    if (t2.ptr > longest) {
      longest = t2.ptr;
      match = ex;
      return ParseCtl.AcceptCont; // always accept lengthenings
    }
    if (ex.valueType() == dest)
      match = ex;
    
    return (ex.valueType() == dest) ? ParseCtl.AcceptCont : ParseCtl.RejectCont;
  }))
    return null;
  
  // confirm
  if (match.valueType() != dest) return null;
  
  text = t2;
  return cast(Object) new RCE(dest, match);
}
mixin DefaultParser!(gotExplicitDefaultCastExpr, "tree.expr.cast_explicit_default", "701");

// casts to types that have conversion defined
Object gotConversionCast(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!t2.accept("cast(")) return null;
  IType dest;
  if (!rest(t2, "type", &dest))
    throw new Exception("No type matched in cast expression: "~t2.next_text());
  if (!t2.accept(")"))
    throw new Exception("Missed closing bracket in cast at "~t2.next_text());
  char* longest;
  if (!rest(t2, "tree.convert", &ex, (Expr ex) {
    return !!(ex.valueType() == dest);
  }))
    return null;
  
  text = t2;
  // override type
  return cast(Object) new RCE(dest, ex);
}
mixin DefaultParser!(gotConversionCast, "tree.expr.cast_convert", "702");

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
