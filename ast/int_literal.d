module ast.int_literal;

import ast.base;

int intconscounter;
class IntExpr : Expr, Literal, HasInfo {
  int num;
  bool isUnsigned;
  string name_used;
  override {
    void emitLLVM(LLVMFile lf) {
      push(lf, num);
    }
    IType valueType() { if (isUnsigned) return Single!(SizeT); return Single!(SysInt); }
    string toString() { return Format(num); }
    string getValue() { return Format(num); }
    string getInfo()  { return Format(num); }
  }
  this(int i, bool iu = false) { num = i; isUnsigned = iu; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
}

IntExpr[int] cache;

IntExpr mkIntObj(int i, bool isUint = false) {
  if (isUint) return fastalloc!(IntExpr)(i, true);
  return fastalloc!(IntExpr)(i);
}

IntExpr mkInt(int i, bool isUint = false) {
  if (i > 1024 || i < -1024) return mkIntObj(i, isUint); // unlikely to be massively common.
  else if (i > 64 && i < -64 && i % nativePtrSize != 0) return mkIntObj(i, isUint);; // dito
  if (!isUint) if (auto p = i in cache) return *p;
  auto res = mkIntObj(i, isUint);
  if (!isUint) cache[i] = res;
  return res;
}

bool gotIntExpr(ref string text, out Expr ex) {
  int i;
  bool isUint;
  return text.gotInt(i, &isUint) && (ex = mkInt(i, isUint), true);
}
