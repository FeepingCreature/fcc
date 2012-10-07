module ast.longmath;

import
  ast.math, ast.tuples, ast.vardecl, ast.base, ast.namespace,
  ast.casting, ast.fun, ast.funcall;

// copypasta from long
class AsmLongBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  override {
    AsmLongBinopExpr dup() { return fastalloc!(AsmLongBinopExpr)(e1.dup, e2.dup, op); }
    void emitLLVM(LLVMFile lf) {
      todo("AsmLongBinopExpr::emitLLVM");
      /+assert(e1.valueType().size == 8);
      assert(e2.valueType().size == 8);
      mixin(mustOffset("8"[]));
      /**
        * e2[1] = d
        * e2[0] = c
        * e1[1] = b
        * e1[0] = a
        **/
      switch (op) {
        case "+":
          e2.emitLLVM(lf); e1.emitLLVM(lf);
          lf.mmove4("(%esp)"[], "%eax"[]);
          lf.mmove4("4(%esp)"[], "%edx"[]);
          lf.mathOp("addl"[], "8(%esp)"[], "%eax"[]);
          lf.mathOp("adcl"[], "12(%esp)"[], "%edx"[]);
          lf.sfree(16);
          lf.pushStack("%edx"[], 4);
          lf.pushStack("%eax"[], 4);
          break;
        case "-":
          e2.emitLLVM(lf); e1.emitLLVM(lf);
          lf.mmove4("(%esp)"[], "%eax"[]);
          lf.mmove4("4(%esp)"[], "%edx"[]);
          lf.mathOp("subl"[], "8(%esp)"[], "%eax"[]);
          lf.mathOp("sbbl"[], "12(%esp)"[], "%edx"[]);
          lf.sfree(16);
          lf.pushStack("%edx"[], 4);
          lf.pushStack("%eax"[], 4);
          break;
        case "*":
          e2.emitLLVM(lf); e1.emitLLVM(lf);
          // (a + f b) * (c + f d) = ac + f(bc + ad) + ff(bd) ^W^W^W^W
          // where f is 2^32
          lf.mmove4("4(%esp)"[], "%eax"[]); // b
          lf.put("imull 8(%esp)"[]); // eax:edx = b*c
          lf.mmove4("%eax"[], "%ecx"[]); // save for later
          lf.mmove4("(%esp)"[], "%eax"[]); // a
          lf.put("imull 12(%esp)"[]); // eax:edx = a*d
          lf.mathOp("addl"[], "%eax"[], "%ecx"[]); // add for later
          lf.mmove4("(%esp)"[], "%eax"[]); // a
          lf.put("mull 8(%esp)"[]); // eax:edx = a*c
          lf.mathOp("addl"[], "%ecx"[], "%edx"[]); // final summation
          lf.sfree(16);
          lf.pushStack("%edx"[], 4);
          lf.pushStack("%eax"[], 4);
          break;
        case "/":
          // defer to cstdlib
          buildFunCall(
            sysmod.lookup("__divdi3"),
            mkTupleExpr(e1, e2), "lldiv math call"
          ).emitLLVM(lf);
          break;
        default:
          logln("Unknown op for long binop expr: "[], op);
          fail;
      }+/
    }
  }
}

static this() { mkLongExpr = (Expr e1, Expr e2, string s) { return cast(BinopExpr) cast(void*) fastalloc!(AsmLongBinopExpr)(e1, e2, s); }; }
