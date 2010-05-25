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

Object gotAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto as = new Assignment;
  Expr ex;
  if (rest(t2, "tree.expr >tree.expr.arith", &ex) && t2.accept("=")) {
    auto lv = cast(LValue) ex;
    if (!lv) throw new Exception(Format("Assignment target is not an lvalue: ", ex, " at ", t2.next_text()));
    as.target = lv;
    if (rest(t2, "tree.expr", &as.value)) {
      text = t2;
      return as;
    } else throw new Exception("While grabbing assignment value at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotAssignment, "tree.semicol_stmt.assign");
