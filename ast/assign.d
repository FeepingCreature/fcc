module ast.assign;

import ast.base, ast.pointer;

class _Assignment(T) : LineNumberedStatementClass {
  T target;
  Expr value;
  bool blind;
  import tools.log;
  this(T t, Expr e, bool force = false, bool blind = false) {
    this.blind = blind;
    if (!force && t.valueType() != e.valueType()) {
      logln("Can't assign: ", t);
      logln(" of ", t.valueType());
      logln(" <- ", e.valueType());
      throw new Exception("Assignment type mismatch! ");
      // asm { int 3; }
    }
    target = t;
    value = e;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(target, value);
  override string toString() { return Format(target, " := ", value, "; "); }
  override void emitAsm(AsmFile af) {
    super.emitAsm(af);
    if (blind) {
      value.emitAsm(af);
      static if (is(T: MValue))
        target.emitAssignment(af);
      else {
        target.emitLocation(af);
        af.popStack("%edx", nativePtrSize);
        af.popStack("(%edx)", value.valueType().size);
        af.nvm("%edx");
      }
    } else {
      mixin(mustOffset("0"));
      int filler;
      auto vt = value.valueType();
      {
        filler = alignStackFor(vt, af);
        mixin(mustOffset("vt.size"));
        value.emitAsm(af);
      }
      static if (is(T: MValue)) {{ // Double-brackets. Trust me.
        mixin(mustOffset("-vt.size"));
        target.emitAssignment(af);
      }} else {
        {
          mixin(mustOffset("nativePtrSize"));
          target.emitLocation(af);
        }
        af.popStack("%edx", nativePtrSize);
        af.popStack("(%edx)", vt.size);
        af.nvm("%edx");
      }
      af.sfree(filler);
    }
  }
}

alias _Assignment!(LValue) Assignment;
alias _Assignment!(MValue) AssignmentM;
import ast.casting;
Object gotAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue lv; MValue mv;
  Expr ex;
  if (rest(t2, "tree.expr _tree.expr.arith", &ex) && t2.accept("=")) {
    Expr value;
    IType[] its;
    if (!rest(t2, "tree.expr", &value)) {
      t2.failparse("Could not parse assignment source");
    }
    auto t3 = t2;
    if (t3.mystripl().length && !t3.accept(";")) {
      t2.failparse("Unknown text after assignment! ");
    }
    
    auto bexup = ex;
    if (!gotImplicitCast(ex, value.valueType(), (Expr ex) {
      if (!fastcast!(LValue) (ex) && !fastcast!(MValue) (ex))
        return false;
      auto ex2 = value;
      auto ev = ex.valueType();
      if (!gotImplicitCast(ex2, ev, (IType it) {
        return test(it == ev);
      })) return false;
      value = ex2;
      return true;
    })) {
      logln("Could not match ", bexup.valueType(), " to ", value.valueType());
      logln("btw backup ex is ", (cast(Object) ex).classinfo.name, ": ", ex);
      t2.failparse("Parsing error");
    }

    lv = fastcast!(LValue) (ex); mv = fastcast!(MValue) (ex);
    if (!lv && !mv) return null;
    
    Expr target;
    if (lv) target = lv;
    else target = mv;
    
    // logln(target.valueType(), " <- ", value.valueType());
    text = t2;
    if (lv)
      return new Assignment(lv, value);
    else
      return new AssignmentM(mv, value);
  } else return null;
}
mixin DefaultParser!(gotAssignment, "tree.semicol_stmt.assign", "1");

static this() {
  registerClass("ast.assign", new Assignment);
}

Statement mkAssignment(Expr to, Expr from) {
  if (auto lv = fastcast!(LValue) (to)) return new Assignment(lv, from);
  if (auto mv = fastcast!(MValue) (to)) return new AssignmentM(mv, from);
  logln("Invalid target for assignment: ", to);
  asm { int 3; }
}
