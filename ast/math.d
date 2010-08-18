module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and, or;

void handlePointers(ref Expr op1, ref Expr op2, bool wtf) {
  if (cast(Pointer) op2.valueType()) {
    if (wtf)
      throw new Exception(Format(op1, " - ", op2, "; wtf kind of bs is that? o.O"));
    swap(op1, op2);
  }
  if (cast(Pointer) op1.valueType()) {
    if (cast(Pointer) op2.valueType())
      throw new Exception("Pointer/pointer addition is undefined! ");
    auto mul = (cast(Pointer) op1.valueType()).target.size;
    op2 = new AsmBinopExpr!("imull")(op2, new IntExpr(mul));
  }
}

bool xor(T)(T a, T b) { return a != b; }

class IntAsFloat : Expr {
  Expr i;
  mixin defaultIterate!(i);
  this(Expr i) { this.i = i; assert(i.valueType() == Single!(SysInt)); }
  override {
    IType valueType() { return Single!(Float); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"));
      i.emitAsm(af);
      // TODO better way
      af.put("fildl (%esp)");
      af.put("fstps (%esp)");
    }
  }
}

Object gotIntAsFloat(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr ^selfrule", &ex))
    return null;
  if (Single!(SysInt) != ex.valueType())
    return null;
  
  text = t2;
  return new IntAsFloat(ex);
}
mixin DefaultParser!(gotIntAsFloat, "tree.expr.int_to_float", "950");

class FloatAsDouble : Expr {
  Expr f;
  mixin defaultIterate!(f);
  this(Expr f) { this.f = f; assert(f.valueType() == Single!(Float)); }
  override {
    IType valueType() { return Single!(Double); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("8"));
      f.emitAsm(af);
      // TODO better way
      af.put("flds (%esp)");
      af.salloc(4);
      af.put("fstpl (%esp)");
    }
  }
}

Object gotFloatAsDouble(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr ^selfrule", &ex))
    return null;
  if (Single!(Float) != ex.valueType())
    return null;
  
  text = t2;
  return new FloatAsDouble(ex);
}
mixin DefaultParser!(gotFloatAsDouble, "tree.expr.float_to_double", "9501");

class AsmBinopExpr(string OP) : Expr {
  Expr e1, e2;
  this(Expr e1, Expr e2) {
    static if (OP == "addl" || OP == "subl")
      handlePointers(e1, e2, OP == "subl");
    if (xor(e1.valueType() == Single!(Float), e2.valueType() == Single!(Float))) {
      if (e1.valueType() == Single!(Float))
        e2 = new IntAsFloat(e2);
      else
        e1 = new IntAsFloat(e1);
    }
    this.e1 = e1;
    this.e2 = e2;
  }
  bool isValid() {
    return
      e1.valueType() == e2.valueType() && e1.valueType() /and/ e2.valueType() == Single!(SysInt) /or/ Single!(Float)
      || cast(Pointer) e1.valueType() && e2.valueType() == Single!(SysInt)
    ;
  }
  mixin defaultIterate!(e1, e2);
  bool isFloatOp() { return !!(e1.valueType() == Single!(Float)); }
  override {
    string toString() {
           static if (OP == "addl")  return Format("(", e1, " + ", e2, ")");
      else static if (OP == "subl")  return Format("(", e1, " - ", e2, ")");
      else static if (OP == "imull") return Format("(", e1, " * ", e2, ")");
      else                           return Format("(", e1, " {", OP, "} ", e2, ")");
    }
    IType valueType() {
      assert(isValid, Format("invalid types: ", e1.valueType(), ", ", e2.valueType()));
      return e1.valueType();
    }
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      e2.emitAsm(af);
      e1.emitAsm(af);
      if (isFloatOp) {
        af.put("flds (%esp)");
        af.sfree(e1.valueType().size);
        static if (OP == "addl")  af.put("fadds (%esp)");
        static if (OP == "subl")  af.put("fsubs (%esp)");
        static if (OP == "imull") af.put("fmuls (%esp)");
        static if (OP == "idivl") af.put("fdivs (%esp)");
        static if (OP == "imodl") assert(false, "Modulo not supported on floats. ");
        af.put("fstps (%esp)");
      } else {
        af.popStack("%eax", e1.valueType());
        
        static if (OP == "idivl" || OP == "imodl") af.put("cdq");
        
        static if (OP == "idivl" || OP == "imodl") af.put("idivl (%esp)");
        else af.mathOp(OP, "(%esp)", "%eax");
        
        static if (OP == "imodl") af.mmove4("%edx", "(%esp)");
        else af.mmove4("%eax", "(%esp)");
      }
    }
  }
}
alias AsmBinopExpr!("addl") AddExpr;
alias AsmBinopExpr!("subl") SubExpr;
alias AsmBinopExpr!("andl") AndExpr;
alias AsmBinopExpr!("orl")  OrExpr;
alias AsmBinopExpr!("imull") MulExpr;

static this() { parsecon.addPrecedence("tree.expr.arith", "1"); }

import ast.pointer, ast.literals, tools.base: swap;
Object gotMathExpr(Ops...)(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  auto old_op = op;
  retry:
  Expr op2;
  foreach (i, bogus; Ops[0 .. $/2]) {
    auto t3 = t2;
    bool accepted = t3.accept(Ops[i*2]);
    if (t3.startsWith(Ops[i*2]))
      accepted = false; // a && b != a & &b (!)
    if (accepted && cont(t3, &op2)) {
      auto binop = new AsmBinopExpr!(Ops[i*2+1])(op, op2);
      if (!binop.isValid()) {
        error = Format("Invalid math op at '", t2.next_text(), "': ", op, " and ", op2);
        continue;
      }
      op = binop;
      t2 = t3;
      goto retry;
    }
  }
  if (op is old_op) {
    // Why would we want arithmetic, but not single values?
    // return null;
    if (op) text = t2;
    return cast(Object) op;
  }
  text = t2;
  return cast(Object) op;
}

alias gotMathExpr!("%", "imodl") gotModExpr;
mixin DefaultParser!(gotModExpr, "tree.expr.arith.mod", "33");

alias gotMathExpr!("+", "addl", "-", "subl") gotAddSubExpr;
mixin DefaultParser!(gotAddSubExpr, "tree.expr.arith.addsub", "31");
alias gotMathExpr!("*", "imull", "/", "idivl") gotMulDivExpr;
mixin DefaultParser!(gotMulDivExpr, "tree.expr.arith.muldiv", "32");

alias gotMathExpr!("|", "orl") gotOrExpr;
mixin DefaultParser!(gotOrExpr, "tree.expr.arith.or", "51");
alias gotMathExpr!("&", "andl") gotAndExpr;
mixin DefaultParser!(gotAndExpr, "tree.expr.arith.and", "52");

// TODO: hook into parser
class CondWrap : Expr {
  Cond cd;
  mixin This!("cd");
  mixin defaultIterate!(cd);
  override {
    IType valueType() {
      return Single!(SysInt); // TODO: bool type
    }
    void emitAsm(AsmFile af) {
      auto past = af.genLabel();
      af.put("xorl %eax, %eax");
      cd.jumpOn(af, false, past);
      af.mmove4("$1", "%eax");
      af.emitLabel(past);
    }
  }
}

Object gotNegExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("-")) return null;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex, (Expr ex) { return !!(ex.valueType() == Single!(SysInt)); }))
    throw new Exception("Found no type match for negation at '"~t2.next_text()~"'");
  text = t2;
  return new SubExpr(new IntExpr(0), ex);
}
mixin DefaultParser!(gotNegExpr, "tree.expr.neg", "213");
