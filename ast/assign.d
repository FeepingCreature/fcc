module ast.assign;

import ast.base, ast.variable, ast.pointer;

class Assignment : Statement {
  LValue target;
  Expr value;
  bool blind;
  import tools.log;
  this(LValue t, Expr e, bool force = false, bool blind = false) {
    this.blind = blind;
    if (!force && t.valueType() != e.valueType()) {
      throw new Exception(Format(
        "Can't assign: ", t, " of ", t.valueType(), " <- ", e.valueType()
      ));
    }
    target = t;
    value = e;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(target, value);
  override string toString() { return Format(target, " := ", value, "; "); }
  override void emitAsm(AsmFile af) {
    if (blind) {
      value.emitAsm(af);
      target.emitLocation(af);
      af.popStack("%eax", new Pointer(target.valueType()));
      af.popStack("(%eax)", value.valueType());
    } else {
      mixin(mustOffset("0"));
      {
        mixin(mustOffset("value.valueType().size"));
        value.emitAsm(af);
      }
      {
        mixin(mustOffset("nativePtrSize"));
        target.emitLocation(af);
      }
      af.popStack("%eax", new Pointer(target.valueType()));
      af.popStack("(%eax)", value.valueType());
    }
  }
}

import ast.casting;
Object gotAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue target;
  Expr ex;
  if (rest(t2, "tree.expr >tree.expr.arith", &ex) && t2.accept("=")) {
    auto lv = cast(LValue) ex;
    if (!lv) return null;
    target = lv;
    Expr value;
    IType[] its;
    if (!rest(t2, "tree.expr", &value) || !gotImplicitCast(value, (IType it) { its ~= it; return test(it == target.valueType()); })) {
      throw new Exception(Format("Mismatching types in assignment: ", target.valueType(), " <- ", its, " @'", t2.next_text(), "'"));
      return null;
    }
    // logln(target.valueType(), " <- ", value.valueType());
    text = t2;
    return new Assignment(target, value);
  } else return null;
}
mixin DefaultParser!(gotAssignment, "tree.semicol_stmt.assign", "1");
