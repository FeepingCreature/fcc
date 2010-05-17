module ast.assign;

import ast.base, ast.variable, ast.pointer;

class Assignment : Statement {
  LValue target;
  Expr value;
  this(LValue t, Expr e) { target = t; value = e; }
  this() { }
  override void emitAsm(AsmFile af) {
    value.emitAsm(af);
    target.emitLocation(af);
    af.popStack("%eax", new Pointer(target.valueType()));
    
    auto size = value.valueType().size;
    assert(0 == (size % 4));
    
    af.popStack("(%eax)", value.valueType());
  }
}
