module ast.longmath;

import ast.math, ast.tuples, ast.vardecl, ast.base, ast.namespace, ast.casting;

// copypasta from long
class AsmLongBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  override {
    AsmLongBinopExpr dup() { return new AsmLongBinopExpr(e1.dup, e2.dup, op); }
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 8);
      assert(e2.valueType().size == 8);
      mixin(mustOffset("8"));
      auto pair = mkTuple(Single!(SysInt), Single!(SysInt));
      e2.emitAsm(af);
      e1.emitAsm(af);
      /**
        * e2[1] = d
        * e2[0] = c
        * e1[1] = b
        * e1[0] = a
        **/
      switch (op) {
        case "+":
          af.mmove4("(%esp)", "%eax");
          af.mmove4("4(%esp)", "%edx");
          af.mathOp("addl", "8(%esp)", "%eax");
          af.mathOp("adcl", "12(%esp)", "%edx");
          af.sfree(16);
          af.pushStack("%edx", 4);
          af.pushStack("%eax", 4);
          break;
        case "*":
          // (a * f b) + (c * f d) = ac + f(bc + ad) + ff(bd) ^W^W^W^W
          // where f is 2^32
          af.mmove4("4(%esp)", "%eax"); // b
          af.put("imull 8(%esp)"); // eax:edx = b*c
          af.mmove4("%eax", "%ecx"); // save for later
          af.mmove4("(%esp)", "%eax"); // a
          af.put("imull 12(%esp)"); // eax:edx = a*d
          af.mathOp("addl", "%eax", "%ecx"); // add for later
          af.mmove4("(%esp)", "%eax"); // a
          af.put("mull 8(%esp)"); // eax:edx = a*c
          af.mathOp("addl", "%ecx", "%edx"); // final summation
          af.sfree(16);
          af.pushStack("%edx", 4);
          af.pushStack("%eax", 4);
          break;
        default:
          logln("Unknown op for long binop expr: ", op);
          fail;
      }
    }
  }
}

static this() { mkLongExpr = (Expr e1, Expr e2, string s) { return cast(BinopExpr) cast(void*) new AsmLongBinopExpr(e1, e2, s); }; }
