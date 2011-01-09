module ast.int_literal;

import ast.base;

class IntExpr : Expr, Literal, HasInfo {
  int num;
  override {
    void emitAsm(AsmFile af) {
      af.pushStack(Format("$", num), valueType());
    }
    IType valueType() { return Single!(SysInt); }
    string toString() { return Format(num); }
    string getValue() { return Format(num); }
    string getInfo()  { return Format(num); }
  }
  this(int i) { num = i; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
}

IntExpr[int] cache;

IntExpr mkInt(int i) {
  if (i > 1024 || i < -1024) return new IntExpr(i); // unlikely to be massively common.
  else if (i > 64 && i < -64 && i % nativePtrSize != 0) return new IntExpr(i); // dito
  if (auto p = i in cache) return *p;
  auto res = new IntExpr(i);
  cache[i] = res;
  return res;
}

bool gotIntExpr(ref string text, out Expr ex) {
  int i;
  return text.gotInt(i) && (ex = mkInt(i), true);
}
