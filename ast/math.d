module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and, or, find;

class IntAsFloat : Expr {
  Expr i;
  this(Expr i) { this.i = i; assert(i.valueType() == Single!(SysInt)); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(i);
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

import ast.casting;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    return new IntAsFloat(ex);
  };
}

class FloatAsInt : Expr {
  Expr f;
  this(Expr f) { this.f = f; assert(f.valueType() == Single!(Float)); }
  private this() { }
  mixin DefaultDup;
  mixin defaultIterate!(f);
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
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    return null;
  auto ex2 = ex;
  // something that casts to float, but not int by itself.
  if (gotImplicitCast(ex2, (IType it) { return test(Single!(SysInt) == it); })
   ||!gotImplicitCast(ex, (IType it) { return test(Single!(Float) == it); }))
    return null;
  
  text = t2;
  return new FloatAsInt(ex);
}
mixin DefaultParser!(gotFloatAsInt, "tree.convert.float_to_int");

class FloatAsDouble : Expr {
  Expr f;
  this(Expr f) { this.f = f; assert(f.valueType() == Single!(Float)); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(f);
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

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(Float) != ex.valueType()) return null;
    return new FloatAsDouble(ex);
  };
}

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
  if (auto be = cast(BinopExpr) ex) {
    if (be.op == "*") {
      string f1 = fold(be.e1), f2 = fold(be.e2);
      if (!f1.startsWith("$") || !f2.startsWith("$")) return null;
      return Format("$", f1[1 .. $].atoi() * f2[1 .. $].atoi());
    }
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

abstract class BinopExpr : Expr {
  Expr e1, e2;
  string op;
  this(Expr e1, Expr e2, string op) {
    if (!e1 || !e2)
      asm { int 3; }
    opt(e1);
    opt(e2);
    this.e1 = e1;
    this.e2 = e2;
    this.op = op;
  }
  private this() {}
  mixin defaultIterate!(e1, e2);
  override {
    string toString() {
      return Format("(", e1, " ", op, " ", e2, ")");
    }
    IType valueType() { // TODO: merge e1, e2
      assert(e1.valueType() == e2.valueType());
      return e1.valueType();
    }
    abstract BinopExpr dup();
    abstract void emitAsm(AsmFile af);
  }
}

class AsmIntBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  AsmIntBinopExpr dup() { return new AsmIntBinopExpr(e1.dup, e2.dup, op); }
  override {
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      if (op == "/" || op == "%") {
        e2.emitAsm(af);
        e1.emitAsm(af);
        af.popStack("%eax", e1.valueType());
        af.put("cdq");
        af.put("idivl (%esp)");
        if (op == "%") af.mmove4("%edx", "(%esp)");
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
        auto asm_op = ["+"[]: "addl"[], "-": "subl", "*": "imull", "/": "idivl", "&": "andl", "|": "orl", "%": "imodl"][op];
        af.mathOp(asm_op, op2, "%eax");
        if (late_alloc) af.salloc(4);
        af.mmove4("%eax", "(%esp)");
      }
    }
  }
}

static this() {
  foldopt ~= delegate Expr(Expr ex) {
    auto aibe = cast(AsmIntBinopExpr) ex;
    if (!aibe) return null;
    auto i1 = cast(IntExpr) ast.fold.fold(aibe.e1), i2 = cast(IntExpr) ast.fold.fold(aibe.e2);
    if (!i1 || !i2) return null;
    switch (aibe.op) {
      case "+": return new IntExpr(i1.num + i2.num);
      case "-": return new IntExpr(i1.num - i2.num);
      case "*": return new IntExpr(i1.num * i2.num);
      case "/": return new IntExpr(i1.num / i2.num);
      default: break;
    }
    return null;
  };
}

class AsmFloatBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  override {
    AsmFloatBinopExpr dup() { return new AsmFloatBinopExpr(e1.dup, e2.dup, op); }
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      // TODO: belongs in optimizer
      bool commutative = op == "+" || op == "*";
      if (commutative) {
        // hackaround for circular dep avoidance
        if ((cast(Object) e2).classinfo.name.find("Variable") != -1 || cast(FloatExpr) e2 || cast(IntAsFloat) e2)
          swap(e1, e2); // try to eval simpler expr last
      }
      loadFloatEx(e2, af);
      loadFloatEx(e1, af);
      af.salloc(4);
      switch (op) {
        case "+": af.floatMath("fadd"); break;
        case "-": af.floatMath("fsub"); break;
        case "*": af.floatMath("fmul"); break;
        case "/": af.floatMath("fdiv"); break;
        case "%": assert(false, "Modulo not supported on floats. ");
      }
      af.storeFloat("(%esp)");
    }
  }
}

static this() {
  bool isInt(IType it) { return test(it == Single!(SysInt)); }
  bool isFloat(IType it) { return test(it == Single!(Float)); }
  bool isPointer(IType it) { return test(cast(Pointer) it); }
  Expr handleIntMath(string op, Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex1, &isInt) || !gotImplicitCast(ex2, &isInt))
      return null;
    return new AsmIntBinopExpr(ex1, ex2, op);
  }
  Expr handlePointerMath(string op, Expr ex1, Expr ex2) {
    if (gotImplicitCast(ex2, &isPointer)) {
      if (op == "-") throw new Exception(Format("WTF R U DOING THAR :( ", ex1, ", ", ex2));
      swap(ex1, ex2);
    }
    if (gotImplicitCast(ex1, &isPointer)) {
      assert(!isPointer(ex2.valueType()));
      auto mul = (cast(Pointer) ex1.valueType()).target.size;
      ex2 = handleIntMath("*", ex2, new IntExpr(mul));
      return new RCE(ex1.valueType(), handleIntMath(op, new RCE(Single!(SysInt), ex1), ex2));
    }
    return null;
  }
  Expr handleFloatMath(string op, Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex1, &isFloat) || !gotImplicitCast(ex2, &isFloat))
      return null;
    
    return new AsmFloatBinopExpr(ex1, ex2, op);
  }
  void defineOps(Expr delegate(string op, Expr, Expr) dg, bool reduced = false) {
    string[] ops;
    if (reduced) ops = ["+", "-"]; // pointer math
    else ops = ["+", "-", "&", "|", "*", "/", "%"];
    foreach (op; ops)
      defineOp(op, op /apply/ dg);
  }
  defineOps(&handleIntMath);
  defineOps(&handlePointerMath, true);
  defineOps(&handleFloatMath);
}

static this() { parsecon.addPrecedence("tree.expr.arith", "12"); }

import ast.pointer, ast.literals, ast.opers, tools.base: swap;
Object gotMathExpr(Ops...)(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  auto old_op = op;
  retry:
  Expr op2;
  foreach (i, bogus; Ops) {
    auto t3 = t2;
    bool accepted = t3.accept(Ops[i]);
    if (t3.startsWith(Ops[i]))
      accepted = false; // a && b != a & &b (!)
    if (accepted) {
      if (cont(t3, &op2)) {
        op = lookupOp(Ops[i], op, op2);
        t2 = t3;
        goto retry;
      } else
        throw new Exception("Could not find operand for '"~Ops[i]~"' at '"~t3.next_text()~"'! ");
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

alias gotMathExpr!("%") gotModExpr;
mixin DefaultParser!(gotModExpr, "tree.expr.arith.mod", "33");

alias gotMathExpr!("+", "-") gotAddSubExpr;
mixin DefaultParser!(gotAddSubExpr, "tree.expr.arith.addsub", "31");
alias gotMathExpr!("*", "/") gotMulDivExpr;
mixin DefaultParser!(gotMulDivExpr, "tree.expr.arith.muldiv", "32");

alias gotMathExpr!("|") gotOrExpr;
mixin DefaultParser!(gotOrExpr, "tree.expr.arith.or", "51");
alias gotMathExpr!("&") gotAndExpr;
mixin DefaultParser!(gotAndExpr, "tree.expr.arith.and", "52");

alias gotMathExpr!("^") gotPowExpr;
mixin DefaultParser!(gotPowExpr, "tree.expr.arith.pow", "34");

// TODO: hook into parser
class CondWrap : Expr {
  Cond cd;
  mixin MyThis!("cd");
  mixin DefaultDup!();
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
  return cast(Object) lookupOp("-", new IntExpr(0), ex);
}
mixin DefaultParser!(gotNegExpr, "tree.expr.neg", "213");
