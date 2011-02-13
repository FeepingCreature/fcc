module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and, or, find, todg;

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
      af.loadIntAsFloat("(%esp)");
      af.storeFloat("(%esp)");
    }
  }
}

import ast.casting, ast.fold, ast.literals, ast.fun;
extern(C) float sqrtf(float);
static this() {
  foldopt ~= delegate Expr(Expr ex) {
    if (auto iaf = fastcast!(IntAsFloat)~ ex) {
      auto i = fold(iaf.i);
      if (auto ie = fastcast!(IntExpr)~ i) {
        return new FloatExpr(ie.num);
      }
    }
    return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto fc = fastcast!(FunCall) (ex)) {
      if (fc.fun.extern_c && fc.fun.name == "sqrtf") {
        assert(fc.params.length == 1);
        auto fe = fc.params[0];
        if (!gotImplicitCast(fe, (Expr ex) { return test(fastcast!(FloatExpr)~ foldex(ex)); }))
          return null;
        return new FloatExpr(sqrtf((fastcast!(FloatExpr)~ foldex(fe)).f));
      }
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    return new IntAsFloat(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Double) != ex.valueType())
      return null;
    return new DoubleAsFloat(ex);
  };
}

class IntAsLong : Expr {
  Expr i;
  this(Expr i) { this.i = i; assert(i.valueType() == Single!(SysInt)); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(i);
  override {
    string toString() { return Format("float(", i, ")"); }
    IType valueType() { return Single!(Long); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("8"));
      (mkInt(0)).emitAsm(af);
      i.emitAsm(af);
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    return new IntAsLong(ex);
  };
}

class FPAsInt : Expr {
  Expr fp;
  bool dbl;
  this(Expr fp, bool dbl = false) {
    this.fp = fp;
    this.dbl = dbl;
    if (dbl)
      assert(fp.valueType() == Single!(Double));
    else
      assert(fp.valueType() == Single!(Float));
  }
  private this() { }
  mixin DefaultDup;
  mixin defaultIterate!(fp);
  override {
    string toString() { return Format("int:", fp); }
    IType valueType() { return Single!(SysInt); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"));
      fp.emitAsm(af);
      if (dbl) af.loadDouble("(%esp)");
      else af.loadFloat("(%esp)");
      if (dbl) af.sfree(4);
      af.put("fistpl (%esp)");
      af.floatStackDepth --;
    }
  }
}

Expr floatToInt(Expr ex, IType) {
  auto ex2 = ex;
  // something that casts to float, but not int by itself.
  if (gotImplicitCast(ex2, (IType it) { return test(Single!(SysInt) == it); })
   ||!gotImplicitCast(ex, (IType it) { return test(Single!(Float) == it); }))
    return null;
  
  return new FPAsInt(ex);
}

Expr doubleToInt(Expr ex, IType) {
  auto ex2 = ex;
  if (gotImplicitCast(ex2, (IType it) { return test(Single!(SysInt) == it); })
   ||!gotImplicitCast(ex, (IType it) { return test(Single!(Double) == it); }))
    return null;
  
  return new FPAsInt(ex, true);
}

static this() {
  converts ~= &floatToInt /todg;
  converts ~= &doubleToInt /todg;
}

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
      af.storeDouble("(%esp)");
    }
  }
}

class DoubleAsFloat : Expr {
  Expr d;
  this(Expr d) { this.d = d; assert(d.valueType() == Single!(Double)); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(d);
  override {
    IType valueType() { return Single!(Float); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"));
      d.emitAsm(af);
      af.loadDouble("(%esp)");
      af.sfree(4);
      af.storeFloat("(%esp)");
    }
  }
}

class IntLiteralAsShort : Expr {
  IntExpr ie;
  this(IntExpr ie) { this.ie = ie; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ie);
  override {
    IType valueType() { return Single!(Short); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("2"));
      af.mmove2(Format("$", ie.num), "%ax");
      af.pushStack("%ax", valueType());
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(Float) != ex.valueType()) return null;
    return new FloatAsDouble(ex);
  };
  // TODO: conversion cast double to float
  implicits ~= delegate Expr(Expr ex) {
    auto dex = fastcast!(DoubleExpr)~ foldex(ex);
    if (!dex) return null;
    return new FloatExpr(cast(float) dex.d);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    auto ie = fastcast!(IntExpr)~ fold(ex);
    if (!ie || ie.num > 65535 || ie.num < -32767) return null;
    return new IntLiteralAsShort(ie);
  };
}

void loadFloatEx(Expr ex, AsmFile af) {
  if (auto lv = fastcast!(CValue)~ ex) {
    lv.emitLocation(af);
    af.popStack("%eax", voidp);
    af.loadFloat("(%eax)");
    af.nvm("%eax");
  } else {
    int toFree = 4 + alignStackFor(ex.valueType(), af);
    ex.emitAsm(af);
    af.loadFloat("(%esp)");
    af.sfree(toFree);
  }
}

void loadDoubleEx(Expr ex, AsmFile af) {
  if (auto cv = fastcast!(CValue)~ ex) {
    cv.emitLocation(af);
    af.popStack("%eax", voidp);
    af.loadDouble("(%eax)");
    af.nvm("%eax");
  } else {
    ex.emitAsm(af);
    af.loadDouble("(%esp)");
    af.sfree(8);
  }
}

void opt(Expr ex) {
  void delegate(ref Iterable) dg;
  dg = (ref Iterable it) {
    it.iterate(dg);
    if (auto iaf = fastcast!(IntAsFloat)~ it) {
      if (auto ie = fastcast!(IntExpr)~ iaf.i) {
        it = new FloatExpr(ie.num);
      }
    }
  };
  ex.iterate(dg);
}

abstract class BinopExpr : Expr, HasInfo {
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
    string getInfo() { return op; }
    IType valueType() { // TODO: merge e1, e2
      assert(e1.valueType() == e2.valueType());
      return e1.valueType();
    }
    abstract BinopExpr dup();
    abstract void emitAsm(AsmFile af);
  }
}

class AsmIntBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) {
    super(e1, e2, op);
  }
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
        af.extendDivide("(%esp)");
        af.sfree(4);
        if (op == "%") {
          af.pushStack("%edx", Single!(SysInt));
          af.nvm("%edx");
        } else {
          af.pushStack("%eax", Single!(SysInt));
          af.nvm("%eax");
        }
      } else {
        string op1, op2;
        if (auto c2 = fastcast!(IntExpr)~ foldex(e2)) {
          op2 = Format("$", c2.num);
        } else {
          op2 = "%ecx";
          e2.emitAsm(af);
        }
        if (auto c1 = fastcast!(IntExpr)~ foldex(e1)) {
          op1 = Format("$", c1.num);
          af.mmove4(op1, "%eax");
        } else {
          e1.emitAsm(af);
          af.popStack("%eax", e1.valueType());
        }
        string top = op;
        if (top == "*" && op2.startsWith("$")) {
          auto num = op2[1 .. $].atoi();
          if (num == 4) { top = "<<"; op2 = "$2"; }
        }
        
        auto asm_op = ([
          "+"[]: "addl"[], "-": "subl",
          "*": "imull", "/": "idivl",
          "&": "andl", "|": "orl",
          "%": "imodl",
          "<<": "shl", ">>": "sar", ">>>": "shr"
        ])[top];
        
        if (op2.isRegister())
          af.popStack(op2, e2.valueType());
        
        if (asm_op == "sar" || asm_op == "shl" || asm_op == "%shr")
          if (op2 == "%ecx")
            op2 = "%cl"; // shl/r really want %cl.
        
        af.mathOp(asm_op, op2, "%eax");
        af.pushStack("%eax", Single!(SysInt));
        af.nvm("%eax");
      }
    }
  }
  static this() {
    foldopt ~= delegate Expr(Expr ex) {
      auto aibe = fastcast!(AsmIntBinopExpr) (ex);
      if (!aibe) return null;
      auto
        e1 = foldex(aibe.e1), ie1 = fastcast!(IntExpr)~ e1,
        e2 = foldex(aibe.e2), ie2 = fastcast!(IntExpr)~ e2;
      if (!ie1 || !ie2) {
        if (e1 !is aibe.e1 || e2 !is aibe.e2) {
          return new AsmIntBinopExpr(e1, e2, aibe.op);
        }
        return null;
      }
      switch (aibe.op) {
        case "+": return mkInt(ie1.num + ie2.num);
        case "-": return mkInt(ie1.num - ie2.num);
        case "*": return mkInt(ie1.num * ie2.num);
        case "/": return mkInt(ie1.num / ie2.num);
        case "%": return mkInt(ie1.num % ie2.num);
        case "<<": return mkInt(ie1.num << ie2.num);
        case ">>": return mkInt(ie1.num >> ie2.num);
        case "&": return mkInt(ie1.num & ie2.num);
        case "|": return mkInt(ie1.num | ie2.num);
        default: assert(false, "can't opt/eval (int) "~aibe.op);
      }
    };
  }
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
        if ((fastcast!(Object)~ e2).classinfo.name.find("Variable") != -1 || fastcast!(FloatExpr)~ e2 || fastcast!(IntAsFloat)~ e2)
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
  static this() {
    foldopt ~= delegate Expr(Expr ex) {
      auto afbe = fastcast!(AsmFloatBinopExpr) (ex);
      if (!afbe) return null;
      auto
        e1 = foldex(afbe.e1), fe1 = fastcast!(FloatExpr)~ e1,
        e2 = foldex(afbe.e2), fe2 = fastcast!(FloatExpr)~ e2;
      if (!fe1 || !fe2) {
        if (e1 !is afbe.e1 || e2 !is afbe.e2)
          return new AsmFloatBinopExpr(e1, e2, afbe.op);
        return null;
      }
      switch (afbe.op) {
        case "+": return new FloatExpr(fe1.f + fe2.f);
        case "-": return new FloatExpr(fe1.f - fe2.f);
        case "*": return new FloatExpr(fe1.f * fe2.f);
        case "/": return new FloatExpr(fe1.f / fe2.f);
        default: assert(false, "can't opt/eval (float) "~afbe.op);
      }
      return null;
    };
  }
}

// copypasta from float
class AsmDoubleBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  override {
    AsmDoubleBinopExpr dup() { return new AsmDoubleBinopExpr(e1.dup, e2.dup, op); }
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 8);
      assert(e2.valueType().size == 8);
      loadDoubleEx(e2, af);
      loadDoubleEx(e1, af);
      af.salloc(8);
      switch (op) {
        case "+": af.floatMath("fadd"); break;
        case "-": af.floatMath("fsub"); break;
        case "*": af.floatMath("fmul"); break;
        case "/": af.floatMath("fdiv"); break;
        case "%": assert(false, "Modulo not supported on floats. ");
      }
      af.storeDouble("(%esp)");
    }
  }
  static this() {
    foldopt ~= delegate Expr(Expr ex) {
      auto adbe = fastcast!(AsmDoubleBinopExpr) (ex);
      if (!adbe) return null;
      auto
        e1 = foldex(adbe.e1), de1 = fastcast!(DoubleExpr)~ e1,
        e2 = foldex(adbe.e2), de2 = fastcast!(DoubleExpr)~ e2;
      if (!de1 || !de2) {
        if (e1 !is adbe.e1 || e2 !is adbe.e2)
          return new AsmDoubleBinopExpr(e1, e2, adbe.op);
        return null;
      }
      switch (adbe.op) {
        case "+": return new DoubleExpr(de1.d + de2.d);
        case "-": return new DoubleExpr(de1.d - de2.d);
        case "*": return new DoubleExpr(de1.d * de2.d);
        case "/": return new DoubleExpr(de1.d / de2.d);
        default: assert(false, "can't opt/eval (double) "~adbe.op);
      }
      return null;
    };
  }
}

static this() {
  bool isInt(IType it) { return test(it == Single!(SysInt)); }
  bool isFloat(IType it) { return test(it == Single!(Float)); }
  bool isDouble(IType it) { return test(it == Single!(Double)); }
  bool isPointer(IType it) { return test(fastcast!(Pointer)~ it); }
  Expr handleIntMath(string op, Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex1, &isInt) || !gotImplicitCast(ex2, &isInt))
      return null;
    return new AsmIntBinopExpr(ex1, ex2, op);
  }
  Expr handlePointerMath(string op, Expr ex1, Expr ex2) {
    auto ex22 = ex2;
    if (gotImplicitCast(ex22, &isPointer)) {
      if (op == "-") {
        return null; // wut
      }
      swap(ex1, ex2);
    }
    if (gotImplicitCast(ex1, &isPointer)) {
      if (isPointer(ex2.valueType())) return null;
      if (fastcast!(Float) (ex2.valueType())) {
        logln(ex1, " ", op, " ", ex2, "; WTF?! ");
        logln("is ", ex1.valueType(), " and ", ex2.valueType());
        fail();
      }
      assert(!isFloat(ex2.valueType()));
      auto mul = (fastcast!(Pointer)~ ex1.valueType()).target.size;
      ex2 = handleIntMath("*", ex2, mkInt(mul));
      if (!ex2) return null;
      return reinterpret_cast(ex1.valueType(), handleIntMath(op, reinterpret_cast(Single!(SysInt), ex1), ex2));
    }
    return null;
  }
  Expr handleFloatMath(string op, Expr ex1, Expr ex2) {
    ex1 = foldex(ex1);
    ex2 = foldex(ex2);
    if (Single!(Double) == ex1.valueType() && !fastcast!(DoubleExpr) (ex1))
      return null;
    
    if (Single!(Double) == ex2.valueType() && !fastcast!(DoubleExpr) (ex2))
      return null;
    
    if (fastcast!(DoubleExpr)~ ex1 && fastcast!(DoubleExpr)~ ex2) return null;
    
    if (!gotImplicitCast(ex1, &isFloat) || !gotImplicitCast(ex2, &isFloat))
      return null;
    
    return new AsmFloatBinopExpr(ex1, ex2, op);
  }
  Expr handleDoubleMath(string op, Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex1, &isDouble) || !gotImplicitCast(ex2, &isDouble))
      return null;
    
    return new AsmDoubleBinopExpr(ex1, ex2, op);
  }
  void defineOps(Expr delegate(string op, Expr, Expr) dg, bool reduced = false) {
    string[] ops;
    if (reduced) ops = ["+", "-"]; // pointer math
    else ops = ["+", "-", "&", "|", "*", "/", "%", "<<", ">>", ">>>"];
    foreach (op; ops)
      defineOp(op, op /apply/ dg);
  }
  defineOps(&handleIntMath);
  defineOps(&handleFloatMath);
  defineOps(&handleDoubleMath);
  defineOps(&handlePointerMath, true);
}

static this() { parsecon.addPrecedence("tree.expr.arith", "12"); }

import ast.pointer, ast.opers, tools.base: swap;
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
      bool isAssignment;
      if (t3.accept("="))
        isAssignment = true;
      bool succeeded;
      if (isAssignment) succeeded = !!rest(t3, "tree.expr", &op2);
      else succeeded = !!cont(t3, &op2);
      if (succeeded) {
        if (isAssignment) {
          op = lookupOp(Ops[i]~"=", op, op2);
          t2 = t3;
          break;
        }
        op = lookupOp(Ops[i], op, op2);
        t2 = t3;
        goto retry;
      } else
        t3.failparse("Could not find operand for '", Ops[i], "'");
    }
  }
  if (op is old_op) {
    // Why would we want arithmetic, but not single values?
    // return null;
    if (op) text = t2;
    return fastcast!(Object)~ op;
  }
  text = t2;
  return fastcast!(Object)~ op;
}

alias gotMathExpr!("%") gotModExpr;
mixin DefaultParser!(gotModExpr, "tree.expr.arith.mod", "33");

alias gotMathExpr!("+", "-") gotAddSubExpr;
mixin DefaultParser!(gotAddSubExpr, "tree.expr.arith.addsub", "31");
alias gotMathExpr!("*", "/") gotMulDivExpr;
mixin DefaultParser!(gotMulDivExpr, "tree.expr.arith.muldiv", "32");
alias gotMathExpr!("<<", ">>") gotShiftExpr;
mixin DefaultParser!(gotShiftExpr, "tree.expr.arith.shift", "34");

alias gotMathExpr!("|") gotOrExpr;
mixin DefaultParser!(gotOrExpr, "tree.expr.arith.or", "51");
alias gotMathExpr!("&") gotAndExpr;
mixin DefaultParser!(gotAndExpr, "tree.expr.arith.and", "52");

alias gotMathExpr!("x") gotTimesExpr;
mixin DefaultParser!(gotTimesExpr, "tree.expr.arith.times", "36");
alias gotMathExpr!("^") gotPowExpr;
mixin DefaultParser!(gotPowExpr, "tree.expr.arith.pow", "35");

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
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Found no expression for negation");
  text = t2;
  if (auto lop = lookupOp("-", true, mkInt(0), ex))
    return fastcast!(Object)~ lop;
  if (auto lop = lookupOp("-", true, ex))
    return fastcast!(Object)~ lop;
  t2.failparse("Found no lookup match for negation of ", ex.valueType());
}
mixin DefaultParser!(gotNegExpr, "tree.expr.neg", "213", "-");
