module ast.literals;

import ast.base, ast.pointer, tools.base: slice, replace;

public import ast.int_literal, ast.float_literal;

import ast.static_arrays, parseBase;

Expr delegate(string) mkString; // defined in literal_string

int dconscounter;

class DoubleExpr : Expr, Literal {
  union {
    double d;
    uint[2] i;
  }
  this(double d) { this.d = d; }
  mixin defaultIterate!();
  string name_used;
  override {
    DoubleExpr dup() { return new DoubleExpr(d); }
    string toString() { return Format(d); }
    IType valueType() { return Single!(Double); }
    string getValue() { assert(false); }
    void emitAsm(AsmFile af) {
      if (!name_used) {
        name_used = af.allocConstant(Format("dcons_", dconscounter ++), cast(ubyte[]) i);
      }
      af.pushStack(qformat("0($", name_used, ")"), 8);
    }
  }
}

int floatconscounter;

class FloatExpr : Expr, Literal {
  union {
    float f;
    uint f_as_i;
  }
  this(float f) { this.f = f; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  string name_used;
  override {
    string toString() { return Format(f); }
    IType valueType() { return Single!(Float); }
    string getValue() { return Format(f_as_i); }
    void emitAsm(AsmFile af) {
      if (!name_used) {
        name_used = af.allocConstantValue(qformat("cons_float_constant_", floatconscounter++, "___xfcc_encodes_", f_as_i), cast(ubyte[]) (&f_as_i)[0 .. 1], true);
      }
      af.pushStack(name_used, 4);
    }
  }
}

bool fpPrecheck(string s) {
  s.eatComments();
  if (!s.length) return false;
  auto ch = s[0];
  if ((ch < '0' || ch > '9') && ch != '.' && ch != '-') { return false; }
  return true;
}

Object gotFloatExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!fpPrecheck(text)) return null;
  float f;
  if (gotFloat(text, f)) return new FloatExpr(f);
  return null;
}
mixin DefaultParser!(gotFloatExpr, "tree.expr.float_literal_early", "230");
mixin DefaultParser!(gotFloatExpr, "tree.expr.literal.float", "54");

Object gotDoubleExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!fpPrecheck(text)) return null;
  double d;
  if (gotDouble(text, d)) return new DoubleExpr(d);
  return null;
}
mixin DefaultParser!(gotDoubleExpr, "tree.expr.literal.double", "545");

Object gotLiteralSuffixExpr(ref string text, ParseCb cont, ParseCb rest) {
  IntExpr res;
  if (!rest(text, "tree.expr.int_literal", &res)) return null;
  if (text.accept("K")) return mkInt(res.num * 1024);
  else if (text.accept("M")) return mkInt(res.num * 1024 * 1024);
  else if (text.accept("G")) return mkInt(res.num * 1024 * 1024 * 1024);
  else return null;
}
mixin DefaultParser!(gotLiteralSuffixExpr, "tree.expr.int_literal_suffix", "2301");

Object gotLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (t2.gotIntExpr(ex)) {
    // allow for a..b .. HAX!
    if (t2.length >= 2) {
      auto t3 = t2;
      char ch1 = t3.takech(' '), ch2 = t3.takech(' ');
      if (ch1 == '.' && ch2 != '.')
        return null;
    }
    text = t2;
    return fastcast!(Object)~ ex;
  } else return null;
}

static this() {
  parsecon.addPrecedence("tree.expr.literal", "55");
}

mixin DefaultParser!(gotLiteralExpr, "tree.expr.int_literal", "23");

/// "foo": char[3] -> char*
class CValueAsPointer : Expr {
  CValue sup;
  this(CValue sup) {
    this.sup = sup;
    if (!sup) asm { int 3; }
  }
  override typeof(this) dup() { return new typeof(this) (sup.dup); }
  mixin defaultIterate!(sup);
  override IType valueType() {
    if (auto sa = fastcast!(StaticArray)~ sup.valueType())
      return new Pointer(sa.elemType);
    throw new Exception(Format("The CValue ", sup, " has confused me. "));
  }
  override void emitAsm(AsmFile af) {
    sup.emitLocation(af);
  }
  override string toString() { return Format("cvalue& ", sup); }
}
