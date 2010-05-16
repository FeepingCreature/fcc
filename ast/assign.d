module ast.assign;

import ast.base, ast.variable, ast.pointer;

class Assignment : Statement {
  LValue target;
  Expr value;
  this(LValue t, Expr e) { target = t; value = e; }
  this() { }
  override void emitAsm(AsmFile af) {
    assert(value.valueType().size == 4);
    value.emitAsm(af);
    target.emitLocation(af);
    af.popStack("%eax", new Pointer(target.valueType()));
    af.popStack("(%eax)", value.valueType());
  }
}
