module ast.assign;

import ast.base, ast.pointer;

class _Assignment(T) : Statement {
  T target;
  Expr value;
  bool blind;
  import tools.log;
  this(T t, Expr e, bool force = false, bool blind = false) {
    this.blind = blind;
    if (!force && t.valueType() != e.valueType()) {
      // asm { int 3; }
      throw new Exception(Format(
        "Can't assign: ", t, " of ", t.valueType(), " <- ", e.valueType()
      ));
    }
    target = t;
    value = e;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(value);
  override string toString() { return Format(target, " := ", value, "; "); }
  override void emitAsm(AsmFile af) {
    if (blind) {
      value.emitAsm(af);
      static if (is(T: MValue))
        target.emitAssignment(af);
      else {
        target.emitLocation(af);
        af.popStack("%eax", new Pointer(target.valueType()));
        af.popStack("(%eax)", value.valueType());
        af.nvm("%eax");
      }
    } else {
      mixin(mustOffset("0"));
      {
        mixin(mustOffset("value.valueType().size"));
        value.emitAsm(af);
      }
      static if (is(T: MValue)) {
        mixin(mustOffset("-value.valueType().size"));
        target.emitAssignment(af);
      } else {
        {
          mixin(mustOffset("nativePtrSize"));
          target.emitLocation(af);
        }
        af.popStack("%eax", new Pointer(target.valueType()));
        af.popStack("(%eax)", value.valueType());
        af.nvm("%eax");
      }
    }
  }
}

alias _Assignment!(LValue) Assignment;

import ast.casting;
Object gotAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue lv; MValue mv;
  Expr ex;
  if (rest(t2, "tree.expr _tree.expr.arith", &ex) && t2.accept("=")) {
    lv = cast(LValue) ex; mv = cast(MValue) ex;
    if (!lv && !mv) return null;
    
    Expr target;
    if (lv) target = lv;
    else target = mv;
    
    Expr value;
    IType[] its;
    if (!rest(t2, "tree.expr", &value)) {
      t2.failparse("Could not parse assignment source");
    }
    auto tv = target.valueType();
    if (!gotImplicitCast(value, tv, (IType it) { its ~= it; return test(it == tv); })) {
      text.failparse("Mismatching types in assignment: ", tv, " <- ", its);
    }
    // logln(target.valueType(), " <- ", value.valueType());
    text = t2;
    if (lv)
      return new Assignment(lv, value);
    else
      return new _Assignment!(MValue)(mv, value);
  } else return null;
}
mixin DefaultParser!(gotAssignment, "tree.semicol_stmt.assign", "1");
