module ast.math;

import ast.base, ast.namespace, parseBase;
import tools.base: This, This_fn, rmSpace, and;

void handlePointers(ref Expr op1, ref Expr op2) {
  if (cast(Pointer) op2.valueType()) {
    swap(op1, op2);
  }
  if (cast(Pointer) op1.valueType()) {
    if (cast(Pointer) op2.valueType())
      throw new Exception("Pointer/pointer addition is undefined! ");
    auto mul = (cast(Pointer) op1.valueType()).target.size;
    op2 = new AsmBinopExpr!("imull")(new IntExpr(mul), op2);
  }
}

class AsmBinopExpr(string OP) : Expr {
  Expr e1, e2;
  this(Expr e1, Expr e2) {
    static if (OP == "addl" || OP == "subl")
      handlePointers(e1, e2);
    this.e1 = e1;
    this.e2 = e2;
  }
  override {
    Type valueType() {
      assert(e1.valueType().size == e2.valueType().size /and/ 4);
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
alias AsmBinopExpr!("addl") AddExpr;
alias AsmBinopExpr!("subl") SubExpr;

static this() { parsecon.addPrecedence("tree.expr.arith", "1"); }

import ast.pointer, ast.literals, tools.base: swap;
Object gotAddSubExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  auto old_op = op;
  retry:
  Expr op2;
  if (t2.accept("+") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("addl")(op, op2);
    goto retry;
  }
  if (t2.accept("-") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("subl")(op, op2);
    goto retry;
  }
  if (op is old_op) return null;
  text = t2;
  return cast(Object) op;
}
mixin DefaultParser!(gotAddSubExpr, "tree.expr.arith.addsub", "1");

Object gotMulDivExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  auto old_op = op;
  retry:
  Expr op2;
  if (t2.accept("*") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("imull")(op, op2);
    goto retry;
  }
  if (t2.accept("/") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("idivl")(op, op2);
    goto retry;
  }
  if (op is old_op) return null;
  text = t2;
  return cast(Object) op;
}
mixin DefaultParser!(gotMulDivExpr, "tree.expr.arith.muldiv", "2");

// TODO: hook into parser
class CondWrap : Expr {
  Cond cd;
  mixin This!("cd");
  override {
    Type valueType() {
      return Single!(SysInt); // TODO: bool type
    }
    void emitAsm(AsmFile af) {
      auto past = af.genLabel();
      af.put("xorl %eax, %eax");
      cd.jumpOn(af, false, past);
      af.mmove4("$1", "%eax");
      af.emitLabel(past);
    }
  }
}
