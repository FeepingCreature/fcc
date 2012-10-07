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
    DoubleExpr dup() { return fastalloc!(DoubleExpr)(d); }
    string toString() { return Format(d); }
    IType valueType() { return Single!(Double); }
    string getValue() { assert(false); }
    void emitLLVM(LLVMFile lf) {
      todo("DoubleExpr::emitLLVM");
      /*if (!name_used) {
        name_used = lf.allocConstant(Format("dcons_"[], dconscounter ++), cast(ubyte[]) i);
      }
      lf.pushStack(qformat("0($"[], name_used, ")"[]), 8);*/
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
    void emitLLVM(LLVMFile lf) {
      todo("FloatExpr::emitLLVM");
      /*if (isARM) {
        lf.mmove4(qformat("="[], f_as_i), lf.regs[0]);
        lf.pushStack(lf.regs[0], 4);
      } else {
        if (!name_used || !(lf).knowsConstant(name_used)) {
          name_used = lf.allocConstantValue(qformat("cons_float_constant_"[], floatconscounter++, "___xfcc_encodes_"[], f_as_i), cast(ubyte[]) (&f_as_i)[0 .. 1], true);
        }
        lf.pushStack(name_used, 4);
      }*/
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
  if (gotFloat(text, f)) return fastalloc!(FloatExpr)(f);
  return null;
}
mixin DefaultParser!(gotFloatExpr, "tree.expr.float_literal_early", "230");
mixin DefaultParser!(gotFloatExpr, "tree.expr.literal.float", "54");

Object gotDoubleExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!fpPrecheck(text)) return null;
  double d;
  if (gotDouble(text, d)) return fastalloc!(DoubleExpr)(d);
  return null;
}
mixin DefaultParser!(gotDoubleExpr, "tree.expr.literal.double", "545");

Object gotLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  int i;
  auto t2 = text;
  if (t2.gotInt(i)) {
    // allow for a..b .. HAX!
    if (t2.length >= 2) {
      auto t3 = t2;
      char ch1 = t3.takech(' '), ch2 = t3.takech(' ');
      if (ch1 == '.' && ch2 != '.')
        return null;
    }
    if (t2.accept("K")) i *= 1024;
    else if (t2.accept("M")) i *= 1024*1024;
    else if (t2.accept("G")) i *= 1024*1024*1024;
    text = t2;
    return fastcast!(Object)(mkInt(i));
  } else return null;
}

static this() {
  addPrecedence("tree.expr.literal", "55");
}

mixin DefaultParser!(gotLiteralExpr, "tree.expr.int_literal", "23");

/// "foo": char[3] -> char*
class CValueAsPointer : Expr {
  CValue sup;
  this(CValue sup) {
    this.sup = sup;
    if (!sup) fail;
    // if (fastcast!(StatementAnd)(sup)) fail;
  }
  override typeof(this) dup() { return new typeof(this) (sup.dup); }
  mixin defaultIterate!(sup);
  override IType valueType() {
    if (auto sa = fastcast!(StaticArray) (resolveType(sup.valueType())))
      return fastalloc!(Pointer)(sa.elemType);
    throw new Exception(Format("The CValue ", sup, " has confused me. "));
  }
  override void emitLLVM(LLVMFile lf) {
    sup.emitLocation(lf);
  }
  override string toString() { return Format("cvalue& ", sup); }
}
