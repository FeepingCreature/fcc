module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and;

void handlePointers(ref Expr op1, ref Expr op2) {
  if (cast(Pointer) op2.valueType()) {
    swap(op1, op2);
  }
  if (cast(Pointer) op1.valueType()) {
    if (cast(Pointer) op2.valueType())
      throw new Exception("Pointer/pointer addition is undefined! ");
    auto mul = (cast(Pointer) op1.valueType()).target.size;
    op2 = new AsmBinopExpr!("imull")(op2, new IntExpr(mul));
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
  mixin defaultIterate!(e1, e2);
  override {
    string toString() {
           static if (OP == "addl")  return Format("(", e1, " + ", e2, ")");
      else static if (OP == "subl")  return Format("(", e1, " - ", e2, ")");
      else static if (OP == "imull") return Format("(", e1, " * ", e2, ")");
      else                           return Format("(", e1, " {", OP, "} ", e2, ")");
    }
    IType valueType() {
      assert(e1.valueType().size == e2.valueType().size /and/ 4);
      return e1.valueType();
    }
    void emitAsm(AsmFile af) {
      assert(e2.valueType().size == 4);
      e2.emitAsm(af);
      e1.emitAsm(af);
      assert(e1.valueType().size == 4);
      af.popStack("%eax", e1.valueType());
      
      static if (OP == "idivl" || OP == "imodl") af.put("cdq");
      
      static if (OP == "idivl" || OP == "imodl") af.put("idivl (%esp)");
      else af.mathOp(OP, "(%esp)", "%eax");
      
      static if (OP == "imodl") af.mmove4("%edx", "(%esp)");
      else af.mmove4("%eax", "(%esp)");
    }
  }
}
alias AsmBinopExpr!("addl") AddExpr;
alias AsmBinopExpr!("subl") SubExpr;
alias AsmBinopExpr!("andl") AndExpr;
alias AsmBinopExpr!("orl")  OrExpr;

static this() { parsecon.addPrecedence("tree.expr.arith", "1"); }

import ast.pointer, ast.literals, tools.base: swap;
Object gotMathExpr(Ops...)(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  auto old_op = op;
  retry:
  Expr op2;
  foreach (i, bogus; Ops[0 .. $/2]) {
    auto t3 = t2;
    bool accepted = t3.accept(Ops[i*2]);
    if (t3.startsWith(Ops[i*2]))
      accepted = false; // a && b != a & &b (!)
    if (accepted && cont(t3, &op2)) {
      op = new AsmBinopExpr!(Ops[i*2+1])(op, op2);
      t2 = t3;
      goto retry;
    }
  }
  if (op is old_op) return null;
  text = t2;
  return cast(Object) op;
}

alias gotMathExpr!("%", "imodl") gotModExpr;
mixin DefaultParser!(gotModExpr, "tree.expr.arith.mod", "33");

alias gotMathExpr!("+", "addl", "-", "subl") gotAddSubExpr;
mixin DefaultParser!(gotAddSubExpr, "tree.expr.arith.addsub", "31");
alias gotMathExpr!("*", "imull", "/", "idivl") gotMulDivExpr;
mixin DefaultParser!(gotMulDivExpr, "tree.expr.arith.muldiv", "32");

alias gotMathExpr!("|", "orl") gotOrExpr;
mixin DefaultParser!(gotOrExpr, "tree.expr.arith.or", "51");
alias gotMathExpr!("&", "andl") gotAndExpr;
mixin DefaultParser!(gotAndExpr, "tree.expr.arith.and", "52");

// TODO: hook into parser
class CondWrap : Expr {
  Cond cd;
  mixin This!("cd");
  mixin defaultIterate!(cd);
  override {
    IType valueType() {
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
