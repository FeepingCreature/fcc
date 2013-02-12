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
      asm { int 3; }
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
    
    push(lf, save(lf, value));
    static if (is(T: MValue)) {
      target.emitAssignment(lf);
    } else {
      target.emitLocation(lf);
      auto dest = lf.pop(), src = lf.pop();
      if (value.valueType().llvmSize() != "0") {
        // use addrspace(1) to preserve null accesses so they can crash properly
        auto basetype = typeToLLVM(target.valueType());
        dest = save(lf, "bitcast ", basetype, "* ", dest, " to ", basetype, " addrspace(1)", "*");
        put(lf, "store ", typeToLLVM(value.valueType()), " ", src, ", ", basetype, " addrspace(1)", "* ", dest);
        // put(lf, "store ", typeToLLVM(value.valueType()), " ", src, ", ", typeToLLVM(target.valueType()), "* ", dest);
      }
    }
  }
}

alias _Assignment!(LValue) Assignment;
alias _Assignment!(MValue) AssignmentM;
import ast.casting, ast.fold;
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
    opt(ex);
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
      t2.failparse("Could not assign\n  ", value.valueType(), "\nto\n  ", bexup.valueType()/*, " (", value, ")"*/);
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
