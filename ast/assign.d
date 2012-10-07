module ast.assign;

import ast.base, ast.pointer;

class SelfAssignmentException : Exception {
  this() { super("self assignment detected"[]); }
}

class _Assignment(T) : LineNumberedStatementClass {
  T target;
  Expr value;
  bool blind;
  import tools.log;
  this(T t, Expr e, bool force = false, bool blind = false) {
    this.blind = blind;
    auto tvt = t.valueType(), evt = e.valueType();
    if (!force && resolveType(tvt) != resolveType(evt)) {
      logln("Can't assign: "[], t);
      logln(" of "[], t.valueType());
      logln(" <- "[], e.valueType());
      breakpoint();
      throw new Exception("Assignment type mismatch! "[]);
    }
    target = t;
    value = e;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(target, value);
  override string toString() { return Format(target, " := "[], value, "; "[]); }
  override void emitLLVM(LLVMFile lf) {
    super.emitLLVM(lf);
    todo("Assignment::emitLLVM");
    /*if (!isARM && value.valueType().size % 4 == 0) {
      static if (is(T: LValue)) {
        if (auto srclv = fastcast!(LValue) (value)) {
          mixin(mustOffset("0"[]));
          target.emitLocation(lf);
          srclv.emitLocation(lf);
          lf.popStack("%eax"[], nativePtrSize);
          lf.popStack("%ecx"[], nativePtrSize);
          // ebx = src, ecx = target
          auto sz = value.valueType().size;
          for (int i = 0; i < sz / 4; ++i) {
            lf.mmove4(qformat(i*4, "(%eax)"[]), "%ebx"[]);
            lf.mmove4("%ebx"[], qformat(i*4, "(%ecx)"[]));
            lf.nvm("%ebx"[]);
          }
          return;
        }
      }
    }
    if (blind) {
      value.emitLLVM(lf);
      static if (is(T: MValue))
        target.emitAssignment(lf);
      else {
        target.emitLocation(lf);
        if (isARM) {
          lf.popStack("r2"[], 4);
          armpop(lf, "r2"[], value.valueType().size);
        } else {
          lf.popStack("%edx"[], nativePtrSize);
          lf.popStack("(%edx)"[], value.valueType().size);
          lf.nvm("%edx"[]);
        }
      }
    } else {
      mixin(mustOffset("0"[]));
      int filler;
      auto vt = value.valueType();
      {
        filler = alignStackFor(vt, lf);
        mixin(mustOffset("vt.size"[]));
        value.emitLLVM(lf);
      }
      static if (is(T: MValue)) {{ // Double-brackets. Trust me.
        mixin(mustOffset("-vt.size"[]));
        target.emitAssignment(lf);
      }} else {
        {
          mixin(mustOffset("nativePtrSize"[]));
          target.emitLocation(lf);
        }
        if (isARM) {
          lf.popStack("r2"[], 4);
          armpop(lf, "r2"[], vt.size);
        } else {
          lf.popStack("%edx"[], nativePtrSize);
          lf.popStack("(%edx)"[], vt.size);
          lf.nvm("%edx"[]);
        }
      }
      lf.sfree(filler);
    }*/
  }
}

alias _Assignment!(LValue) Assignment;
alias _Assignment!(MValue) AssignmentM;
import ast.casting;
Object gotAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  LValue lv; MValue mv;
  Expr ex;
  if (rest(t2, "tree.expr _tree.expr.arith"[], &ex) && t2.accept("="[])) {
    Expr value;
    IType[] its;
    if (!rest(t2, "tree.expr"[], &value)) {
      t2.failparse("Could not parse assignment source"[]);
    }
    auto t3 = t2;
    if (t3.mystripl().length && !t3.acceptTerminatorSoft()) {
      t2.failparse("Unknown text after assignment! "[]);
    }
    
    auto bexup = ex;
    bool thereWereAssignables;
    if (!gotImplicitCast(ex, value.valueType(), (Expr ex) {
      if (!fastcast!(LValue) (ex) && !fastcast!(MValue) (ex))
        return false;
      thereWereAssignables = true;
      
      auto ex2 = value;
      auto ev = ex.valueType();
      if (!gotImplicitCast(ex2, ev, (IType it) {
        return test(it == ev);
      })) return false;
      value = ex2;
      return true;
    })) {
      if (!thereWereAssignables) // this was never an assignment
        return null;
      // logln("Could not match "[], bexup.valueType(), " to "[], value.valueType());
      // logln("(note: "[], (fastcast!(Object) (bexup.valueType())).classinfo.name, ")"[]);
      // logln("(note 2: "[], bexup.valueType() == value.valueType(), ")"[]);
      // logln("btw backup ex is "[], (cast(Object) ex).classinfo.name, ": "[], ex);
      t2.failparse("Could not match "[], bexup.valueType(), " to "[], value.valueType());
      // setError(t2, "Could not match "[], bexup.valueType(), " to "[], value.valueType());
      // return null;
      // t2.failparse("Parsing error"[]);
    }

    lv = fastcast!(LValue) (ex); mv = fastcast!(MValue) (ex);
    if (!lv && !mv) return null;
    
    Expr target;
    if (lv) target = lv;
    else target = mv;
    
    // logln(target.valueType(), " <- "[], value.valueType());
    LineNumberedStatementClass res;
    try {
      if (lv)
        res = fastalloc!(Assignment)(lv, value);
      else
        res = fastalloc!(AssignmentM)(mv, value);
    } catch (Exception ex) {
      text.failparse(ex);
    }
    res.configPosition(text);
    text = t2;
    return res;
  } else return null;
}
mixin DefaultParser!(gotAssignment, "tree.semicol_stmt.assign"[], "1"[]);

static this() {
  registerClass("ast.assign"[], new Assignment);
  registerClass("ast.assign"[], new AssignmentM);
}

Statement mkAssignment(Expr to, Expr from) {
  if (from is to) {
    throw new SelfAssignmentException;
  }
  if (auto lv = fastcast!(LValue) (to)) return fastalloc!(Assignment)(lv, from);
  if (auto mv = fastcast!(MValue) (to)) return fastalloc!(AssignmentM)(mv, from);
  logln("Invalid target for assignment: "[], to);
  fail;
}

void emitAssign(LLVMFile lf, LValue target, Expr source, bool force = false, bool blind = false) {
  scope as = new Assignment(target, source, force, blind);
  as.emitLLVM(lf);
}
