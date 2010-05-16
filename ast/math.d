module ast.math;

import ast.base, ast.namespace;
import tools.base: This, This_fn, rmSpace;

class AsmBinopExpr(string OP) : Expr {
  Expr e1, e2;
  mixin This!("e1, e2");
  override {
    Type valueType() {
      assert(e1.valueType() is e2.valueType());
      return e1.valueType();
    }
    void emitAsm(AsmFile af) {
      assert(e2.valueType().size == 4);
      e2.emitAsm(af);
      e1.emitAsm(af);
      assert(e1.valueType().size == 4);
      af.popStack("%eax", e1.valueType());
      
      static if (OP == "idivl") af.put("cdq");
      
      static if (OP == "idivl") af.put("idivl (%esp)");
      else af.mathOp(OP, "(%esp)", "%eax");
      
      af.mmove4("%eax", "(%esp)");
    }
  }
}

class CondWrap : Expr {
  Cond cd;
  mixin This!("cd");
  override {
    Type valueType() {
      return tmemo(new SysInt); // TODO: bool type
    }
    void emitAsm(AsmFile af) {
      cd.emitAsm(af);
      auto past = af.genLabel();
      af.put("xorl %eax, %eax");
      cd.jumpFalse(af, past);
      af.mmove4("$1", "%eax");
      af.emitLabel(past);
    }
  }
}
