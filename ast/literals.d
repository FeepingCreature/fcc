module ast.literals;

import ast.base, ast.pointer, tools.base: slice, replace;

public import ast.int_literal;

import ast.static_arrays, parseBase;

CValue delegate(string) mkString; // defined in literal_string

class FloatExpr : Expr {
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
    void emitAsm(AsmFile af) {
      if (!name_used) {
        name_used = Format("cons_", af.constants.length);
        af.constants[name_used] = cast(ubyte[]) (&f_as_i)[0 .. 1];
      }
      af.pushStack(name_used, valueType());
    }
  }
}

Object gotFloatExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  int i;
  if (!t2.gotInt(i)) return null;
  float f = i;
  if (!t2.length || t2[0] != '.') return null;
  t2.take();
  float weight = 0.1;
  bool gotDigit;
  while (t2.length) {
    auto digit = t2[0];
    if (digit < '0' || digit > '9') break;
    gotDigit = true;
    int d = t2.take() - '0';
    if (f < 0) f -= weight * d;
    else f += weight * d;
    weight /= 10;
  }
  if (!gotDigit) return null;
  text = t2;
  return new FloatExpr(f);
}
mixin DefaultParser!(gotFloatExpr, "tree.expr.literal.float", "54");

string subst(string s, string kind) {
  if (kind == "`") return s;
  assert(kind == "\"");
  return s.replace(`\n`, "\n");
}

Object gotLiteralSuffixExpr(ref string text, ParseCb cont, ParseCb rest) {
  IntExpr res;
  if (!rest(text, "tree.expr.literal", &res)) return null;
  if (text.accept("K")) return new IntExpr(res.num * 1024);
  else if (text.accept("M")) return new IntExpr(res.num * 1024 * 1024);
  else if (text.accept("G")) return new IntExpr(res.num * 1024 * 1024 * 1024);
  else return null;
}
mixin DefaultParser!(gotLiteralSuffixExpr, "tree.expr.literal_suffix", "54");

Object gotLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (text.gotIntExpr(ex)) return cast(Object) ex;
  else return null;
}
mixin DefaultParser!(gotLiteralExpr, "tree.expr.literal", "55");

/// "foo": char[3] -> char*
class CValueAsPointer : Expr {
  CValue sup;
  mixin MyThis!("sup");
  mixin DefaultDup!();
  mixin defaultIterate!(sup);
  override IType valueType() {
    if (auto sa = cast(StaticArray) sup.valueType())
      return new Pointer(sa.elemType);
    throw new Exception(Format("The CValue ", sup, " has confused me. "));
  }
  override void emitAsm(AsmFile af) {
    sup.emitLocation(af);
  }
}

import ast.casting, ast.fold;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto cv = cast(CValue) ex;
    if (!cv || !cast(StaticArray) cv.valueType()) return null;
    return new CValueAsPointer(cv);
  };
}
