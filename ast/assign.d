module ast.assign;

import ast.base, ast.variable, ast.pointer;

class Assignment : Statement {
  LValue target;
  Expr value;
  import tools.log;
  this(LValue t, Expr e) {
    if (t.valueType() != e.valueType())
      throw new Exception(Format("Can't assign: ", t, " <- ", e.valueType()));
    target = t;
    value = e;
  }
  override void emitAsm(AsmFile af) {
    value.emitAsm(af);
    target.emitLocation(af);
    af.popStack("%eax", new Pointer(target.valueType()));
    
    auto size = value.valueType().size;
    assert(0 == (size % 4));
    
    af.popStack("(%eax)", value.valueType());
  }
}

import tools.log;
Object gotAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue target;
  Expr ex;
  logln("try on ", t2.next_text());
  auto forb = rest(t2, "tree.expr >tree.expr.arith", &ex);
  logln("got ", ex, " and ", forb);
  if (ex && t2.accept("=")) {
    logln("murble ", t2.next_text());
    auto lv = cast(LValue) ex;
    if (!lv) throw new Exception(Format("Assignment target is not an lvalue: ", ex, " at ", t2.next_text()));
    target = lv;
    Expr value;
    if (rest(t2, "tree.expr", &value)) {
      if (target.valueType() != value.valueType()) {
        throw new Exception(Format("Mismatching types in assignment: ", target, " <- ", value.valueType()));
      }
      text = t2;
      return new Assignment(target, value);
    } else throw new Exception("While grabbing assignment value at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotAssignment, "tree.semicol_stmt.assign");
