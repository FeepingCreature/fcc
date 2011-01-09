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
    if (auto iaf = cast(IntAsFloat) ex) {
      auto i = fold(iaf.i);
      if (auto ie = cast(IntExpr) i) {
        return new FloatExpr(ie.num);
      }
    }
    return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto fc = cast(FunCall) ex) {
      if (fc.fun.extern_c && fc.fun.name == "sqrtf") {
        assert(fc.params.length == 1);
        auto fe = fc.params[0];
        if (!gotImplicitCast(fe, (Expr ex) { return test(cast(FloatExpr) foldex(ex)); }))
          return null;
        return new FloatExpr(sqrtf((cast(FloatExpr) foldex(fe)).f));
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

class FloatAsInt : Expr {
  Expr f;
  this(Expr f) { this.f = f; assert(f.valueType() == Single!(Float)); }
  private this() { }
  mixin DefaultDup;
  mixin defaultIterate!(f);
  override {
    string toString() { return Format("int(", f, ")"); }
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

Expr floatToInt(Expr ex, IType) {
  auto ex2 = ex;
  // something that casts to float, but not int by itself.
  if (gotImplicitCast(ex2, (IType it) { return test(Single!(SysInt) == it); })
   ||!gotImplicitCast(ex, (IType it) { return test(Single!(Float) == it); }))
    return null;
  
  return new FloatAsInt(ex);
}

static this() {
  converts ~= &floatToInt /todg;
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
    auto dex = cast(DoubleExpr) foldex(ex);
    if (!dex) return null;
    return new FloatExpr(cast(float) dex.d);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    auto ie = cast(IntExpr) fold(ex);
    if (!ie || ie.num > 65535 || ie.num < -32767) return null;
    return new IntLiteralAsShort(ie);
  };
}

void loadFloatEx(Expr ex, AsmFile af) {
  if (auto lv = cast(CValue) ex) {
    lv.emitLocation(af);
    af.popStack("%eax", voidp);
    af.loadFloat("(%eax)");
    af.nvm("%eax");
  } else {
    ex.emitAsm(af);
    af.loadFloat("(%esp)");
    af.sfree(4);
  }
}

void loadDoubleEx(Expr ex, AsmFile af) {
  if (auto cv = cast(CValue) ex) {
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
    if (auto iaf = cast(IntAsFloat) it) {
      if (auto ie = cast(IntExpr) iaf.i) {
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
        if (auto c2 = cast(IntExpr) foldex(e2)) {
          op2 = Format("$", c2.num);
        } else {
          op2 = "%ecx";
          e2.emitAsm(af);
        }
        if (auto c1 = cast(IntExpr) foldex(e1)) {
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
        
        if (asm_op == "sal" || asm_op == "sar" || asm_op == "%shr")
          if (op2 == "%ecx")
            op2 = "%cl"; // shl/r really want %cl.
        
        af.mathOp(asm_op, op2, "%eax");
        af.pushStack("%eax", Single!(SysInt));
        af.nvm("%eax");
      }
    }
  }
  static this() {
    foldopt ~= delegate Itr(Itr it) {
      auto aibe = cast(AsmIntBinopExpr) it;
      if (!aibe) return null;
      auto
        e1 = cast(IntExpr) foldex(aibe.e1),
        e2 = cast(IntExpr) foldex(aibe.e2);
      if (!e1 || !e2) return null;
      switch (aibe.op) {
        case "+": return mkInt(e1.num + e2.num);
        case "-": return mkInt(e1.num - e2.num);
        case "*": return mkInt(e1.num * e2.num);
        case "/": return mkInt(e1.num / e2.num);
        case "%": return mkInt(e1.num % e2.num);
        case "<<": return mkInt(e1.num << e2.num);
        case ">>": return mkInt(e1.num >> e2.num);
        case "&": return mkInt(e1.num & e2.num);
        case "|": return mkInt(e1.num | e2.num);
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
  static this() {
    foldopt ~= delegate Expr(Expr ex) {
      auto afbe = cast(AsmFloatBinopExpr) ex;
      if (!afbe) return null;
      auto
        e1 = cast(FloatExpr) foldex(afbe.e1),
        e2 = cast(FloatExpr) foldex(afbe.e2);
      if (!e1 || !e2) return null;
      switch (afbe.op) {
        case "+": return new FloatExpr(e1.f + e2.f);
        case "-": return new FloatExpr(e1.f - e2.f);
        case "*": return new FloatExpr(e1.f * e2.f);
        case "/": return new FloatExpr(e1.f / e2.f);
        default: assert(false, "can't opt/eval (float) "~afbe.op);;
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
      auto adbe = cast(AsmDoubleBinopExpr) ex;
      if (!adbe) return null;
      auto
        e1 = cast(DoubleExpr) foldex(adbe.e1),
        e2 = cast(DoubleExpr) foldex(adbe.e2);
      if (!e1 || !e2) return null;
      switch (adbe.op) {
        case "+": return new DoubleExpr(e1.d + e2.d);
        case "-": return new DoubleExpr(e1.d - e2.d);
        case "*": return new DoubleExpr(e1.d * e2.d);
        case "/": return new DoubleExpr(e1.d / e2.d);
        default: assert(false, "can't opt/eval (double) "~adbe.op);;
      }
      return null;
    };
  }
}

static this() {
  bool isInt(IType it) { return test(it == Single!(SysInt)); }
  bool isFloat(IType it) { return test(it == Single!(Float)); }
  bool isDouble(IType it) { return test(it == Single!(Double)); }
  bool isPointer(IType it) { return test(cast(Pointer) it); }
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
      if (cast(Float) ex2.valueType()) { logln(ex1, " ", op, " ", ex2, "; WTF?! "); asm { int 3; } }
      assert(!isFloat(ex2.valueType()));
      auto mul = (cast(Pointer) ex1.valueType()).target.size;
      ex2 = handleIntMath("*", ex2, mkInt(mul));
      if (!ex2) return null;
      return new RCE(ex1.valueType(), handleIntMath(op, new RCE(Single!(SysInt), ex1), ex2));
    }
    return null;
  }
  Expr handleFloatMath(string op, Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex1, &isFloat) || !gotImplicitCast(ex2, &isFloat))
      return null;
    
    if (Single!(Double) == ex1.valueType() || Single!(Double) == ex2.valueType())
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
  defineOps(&handlePointerMath, true);
  defineOps(&handleFloatMath);
  defineOps(&handleDoubleMath);
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
      if (cont(t3, &op2)) {
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
    return cast(Object) lop;
  if (auto lop = lookupOp("-", true, ex))
    return cast(Object) lop;
  t2.failparse("Found no lookup match for negation of ", ex.valueType());
}
mixin DefaultParser!(gotNegExpr, "tree.expr.neg", "213", "-");
