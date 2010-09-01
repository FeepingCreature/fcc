module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and, or, find;

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
    string toString() { return Format("float(", i, ")"); }
    IType valueType() { return Single!(Float); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"));
      i.emitAsm(af);
      // TODO better way
      af.put("fildl (%esp)");
      af.floatStackDepth ++;
      af.storeFloat("(%esp)");
    }
  }
}

Object gotIntAsFloat(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr >tree.expr.arith ^selfrule", &ex))
    return null;
  
  if (Single!(SysInt) != ex.valueType())
    return null;
  
  text = t2;
  return new IntAsFloat(ex);
}
mixin DefaultParser!(gotIntAsFloat, "tree.expr.int_to_float", "9021");

class FloatAsInt : Expr {
  Expr f;
  mixin defaultIterate!(f);
  this(Expr f) { this.f = f; assert(f.valueType() == Single!(Float)); }
  override {
    IType valueType() { return Single!(SysInt); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"));
      f.emitAsm(af);
      af.loadFloat("(%esp)");
      af.put("fistpl (%esp)");
      af.floatStackDepth --;
    }
  }
}

Object gotFloatAsInt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr >tree.expr.arith", &ex))
    return null;
  if (Single!(Float) != ex.valueType())
    return null;
  
  text = t2;
  return new FloatAsInt(ex);
}
mixin DefaultParser!(gotFloatAsInt, "tree.convert.float_to_int");

class FloatAsDouble : Expr {
  Expr f;
  mixin defaultIterate!(f);
  this(Expr f) { this.f = f; assert(f.valueType() == Single!(Float)); }
  override {
    IType valueType() { return Single!(Double); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("8"));
      f.emitAsm(af);
      af.loadFloat("(%esp)");
      af.salloc(4);
      af.put("fstpl (%esp)");
      af.floatStackDepth --;
    }
  }
}

Object gotFloatAsDouble(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr ^selfrule", &ex, (Expr ex) { return !!(Single!(Float) == ex.valueType()); }))
    return null;
  
  text = t2;
  return new FloatAsDouble(ex);
}
mixin DefaultParser!(gotFloatAsDouble, "tree.expr.float_to_double", "9501");

void loadFloatEx(Expr ex, AsmFile af) {
  if (auto lv = cast(CValue) ex) {
    lv.emitLocation(af);
    af.popStack("%eax", voidp);
    af.loadFloat("(%eax)");
  } else {
    ex.emitAsm(af);
    af.loadFloat("(%esp)");
    af.sfree(4);
  }
}

string fold(Expr ex) {
  if (auto ie = cast(IntExpr) ex) {
    return Format("$", ie.num);
  }
  if (auto re = cast(IRegister) ex) {
    return "%"~re.getReg();
  }
  if (auto me = cast(MulExpr) ex) {
    string f1 = fold(me.e1), f2 = fold(me.e2);
    if (!f1.startsWith("$") || !f2.startsWith("$")) return null;
    return Format("$", f1[1 .. $].atoi() * f2[1 .. $].atoi());
  }
  return null;
}

void opt(Expr ex) {
  void delegate(ref Iterable) dg;
  dg = (ref Iterable it) {
    it.iterate(dg);
    if (auto iaf = cast(IntAsFloat) it) {
      if (auto ie = cast(IntExpr) iaf.i) {
        it = new FloatExpr(ie.num);
      }
    }
  };
  ex.iterate(dg);
}

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
    opt(e1); opt(e2);
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
      if (isFloatOp) {
        bool commutative = OP == "addl" || OP == "imull";
        if (commutative) {
          // hackaround for circular dep avoidance
          if ((cast(Object) e2).classinfo.name.find("Variable") != -1 || cast(FloatExpr) e2 || cast(IntAsFloat) e2)
            swap(e1, e2); // try to eval simpler expr last
        }
        loadFloatEx(e2, af);
        loadFloatEx(e1, af);
        af.salloc(4);
        static if (OP == "addl")  af.floatMath("fadd");
        static if (OP == "subl")  af.floatMath("fsub");
        static if (OP == "imull") af.floatMath("fmul");
        static if (OP == "idivl") af.floatMath("fdiv");
        static if (OP == "imodl") assert(false, "Modulo not supported on floats. ");
        af.storeFloat("(%esp)");
      } else {
        static if (OP == "idivl" || OP == "imodl") {
          e2.emitAsm(af);
          e1.emitAsm(af);
          af.popStack("%eax", e1.valueType());
          af.put("cdq");
          af.put("idivl (%esp)");
          static if (OP == "imodl") af.mmove4("%edx", "(%esp)");
          else af.mmove4("%eax", "(%esp)");
        } else {
          string op1, op2;
          bool late_alloc;
          if (auto c2 = fold(e2)) {
            op2 = c2;
            late_alloc = true;
          } else {
            op2 = "(%esp)";
            e2.emitAsm(af);
          }
          if (auto c1 = fold(e1)) {
            op1 = c1;
            af.mmove4(op1, "%eax");
          } else {
            e1.emitAsm(af);
            af.popStack("%eax", e1.valueType());
          }
          
          af.mathOp(OP, op2, "%eax");
          if (late_alloc) af.salloc(4);
          af.mmove4("%eax", "(%esp)");
        }
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
    if (accepted) {
      if (cont(t3, &op2)) {
        auto binop = new AsmBinopExpr!(Ops[i*2+1])(op, op2);
        if (!binop.isValid()) {
          error = Format("Invalid math op at '", t2.next_text(), "': ", op, " and ", op2);
          continue;
        }
        op = binop;
        t2 = t3;
        goto retry;
      } else
        throw new Exception("Could not find operand for '"~Ops[i*2]~"' at '"~t3.next_text()~"'! ");
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
  if (!rest(t2, "tree.expr", &ex, (Expr ex) { return !!(ex.valueType() == Single!(SysInt) || ex.valueType() == Single!(Float)); }))
    throw new Exception("Found no type match for negation at '"~t2.next_text()~"'");
  text = t2;
  return new SubExpr(new IntExpr(0), ex);
}
mixin DefaultParser!(gotNegExpr, "tree.expr.neg", "213");
