module ast.longmath;

import
  ast.math, ast.tuples, ast.vardecl, ast.base, ast.namespace,
  ast.casting, ast.fun, ast.funcall;

// copypasta from long
class AsmLongBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  mixin defaultCollapse!(); // TODO fold
  override {
    AsmLongBinopExpr dup() { return fastalloc!(AsmLongBinopExpr)(e1.dup, e2.dup, op); }
    void emitLLVM(LLVMFile lf) {
      assert(e1.valueType().llvmType() == "i64");
      assert(e2.valueType().llvmType() == "i64");
      auto v1 = save(lf, e1), v2 = save(lf, e2);
      string cmd;
      switch (op) {
        case "+": cmd = "add"; break;
        case "-": cmd = "sub"; break;
        case "*": cmd = "mul"; break;
        case "/": cmd = "sdiv"; break;
        case "xor":cmd= "xor"; break;
        case "&": cmd = "and"; break;
        case "|": cmd = "or" ; break;
        case "%": cmd = "urem";break;
        case "<<":cmd = "shl"; break;
        case ">>":cmd = "ashr";break;
        case ">>>":cmd= "lshr";break;
      }
      load(lf, cmd, " i64 ", v1, ", ", v2);
    }
  }
}

static this() { mkLongExpr = (Expr e1, Expr e2, string s) { return cast(BinopExpr) cast(void*) fastalloc!(AsmLongBinopExpr)(e1, e2, s); }; }
