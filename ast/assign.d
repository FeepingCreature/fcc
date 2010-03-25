module ast.assign;

import ast.base, ast.variable;

class Assignment : Statement {
  Variable target;
  Expr value;
  this(Variable v, Expr e) { target = v; value = e; }
  this() { }
  override void emitAsm(AsmFile af) {
    assert(value.valueType().size == 4);
    value.emitAsm(af);
    af.mmove4("(%esp)", "%edx");
    af.mmove4("%edx", Format(target.baseOffset, "(%ebp)"));
    af.sfree(value.valueType().size);
  }
}
