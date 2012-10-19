module ast.int_literal;

import ast.base;

int intconscounter;
class IntExpr : Expr, Literal, HasInfo {
  int num;
  string name_used;
  override {
    void emitLLVM(LLVMFile lf) {
      push(lf, num);
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
  if (i > 1024 || i < -1024) return fastalloc!(IntExpr)(i); // unlikely to be massively common.
  else if (i > 64 && i < -64 && i % nativePtrSize != 0) return fastalloc!(IntExpr)(i); // dito
  if (auto p = i in cache) return *p;
  auto res = fastalloc!(IntExpr)(i);
  cache[i] = res;
  return res;
}

bool gotIntExpr(ref string text, out Expr ex) {
  int i;
  return text.gotInt(i) && (ex = mkInt(i), true);
}
