module ast.int_literal;

import ast.base;

int intconscounter;
class IntExpr : Expr, Literal, HasInfo {
  int num;
  string name_used;
  override {
    void emitAsm(AsmFile af) {
      if (isARM) {
        if (num < 256 && num > -256) {
          af.mmove4(Format("#", num), "r0");
        } else {
          if (!name_used) {
            string numstr;
            if (num >= 0) numstr = qformat(num);
            else if (num == -0x8000_0000) numstr = "minus_2147483648";
            else numstr = qformat("minus_", -num);
            name_used = af.allocConstantValue(qformat("cons_int_constant_", intconscounter++, "___xfcc_encodes_", numstr), cast(ubyte[]) (&num)[0 .. 1], true);
          }
          af.mmove4(Format("=", name_used), "r0");
          af.mmove4("[r0]", "r0");
        }
        af.pushStack("r0", 4);
      } else {
        af.pushStack(Format("$", num), 4);
      }
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
