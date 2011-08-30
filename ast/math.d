module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and, or, find, todg;

Object function(ref string, Object, bool, bool, ParseCb, ParseCb) getPropertiesFn;
void function(void delegate(bool, bool)) withPropcfgFn;

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
      af.loadIntAsFloat("(%esp)");
      af.storeFloat("(%esp)");
    }
  }
}

class LongAsDouble : Expr {
  Expr l;
  this(Expr l) { this.l = l; assert(l.valueType() == Single!(Long)); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(l);
  override {
    string toString() { return Format("double(", l, ")"); }
    IType valueType() { return Single!(Double); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("8"));
      l.emitAsm(af);
      af.loadLongAsFloat("(%esp)");
      af.storeDouble("(%esp)");
    }
  }
}

import ast.casting, ast.fold, ast.literals, ast.fun;
extern(C) float sqrtf(float);
static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto iaf = fastcast!(IntAsFloat) (it)) {
      auto i = fold(iaf.i);
      if (auto ie = fastcast!(IntExpr)~ i) {
        return new FloatExpr(ie.num);
      }
    }
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto fc = fastcast!(FunCall) (it)) {
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
    if (Single!(SysInt) != resolveType(ex.valueType())) return null;
    return new IntAsFloat(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Long) != resolveType(ex.valueType())) return null;
    return new LongAsDouble(ex);
  };
}

class IntAsLong : Expr {
  Expr i;
  this(Expr i) { this.i = i; assert(i.valueType() == Single!(SysInt)); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(i);
  override {
    string toString() { return Format("long(", i, ")"); }
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
      af.storeFPAsInt("(%esp)");
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
  this(Expr d) {
    this.d = d;
    if (resolveTup(d.valueType()) != Single!(Double)) asm { int 3; }
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(d);
  override {
    IType valueType() { return Single!(Float); }
    string toString() { return Format("float:", d); }
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
    string toString() { return Format("short:", ie); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("2"));
      af.mmove2(Format("$", ie.num), "%ax");
      af.pushStack("%ax", 2);
    }
  }
}

class IntLiteralAsByte : Expr {
  IntExpr ie;
  this(IntExpr ie) { this.ie = ie; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ie);
  override {
    IType valueType() { return Single!(Byte); }
    string toString() { return Format("byte:", ie); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("1"));
      af.salloc(1);
      af.mmove1(Format("$", ie.num), "(%esp)");
    }
  }
}

class IntAsShort : Expr {
  Expr ex;
  this(Expr ex) { this.ex = ex; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override {
    IType valueType() { return Single!(Short); }
    string toString() { return Format("short:", ex); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("2"));
      ex.emitAsm(af);
      af.popStack("%eax", 4);
      af.mmove4("%eax", "%ebx");
      af.mathOp("shrl", "$16", "%ebx"); // move eah into eal
      af.mathOp("andw", "$32768", "%bx"); // select high bit
      af.mathOp("andw", "$32767", "%ax"); // mask out high bit
      af.mathOp("orw", "%bx", "%ax"); // copy bit
      af.pushStack("%ax", 2);
    }
  }
}

class ShortAsByte : Expr {
  Expr ex;
  this(Expr ex) { this.ex = ex; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  override {
    IType valueType() { return Single!(Char); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("1"));
      ex.emitAsm(af);
      af.popStack("%ax", 2);
      af.pushStack("%al", 1);
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(Float) != ex.valueType()) return null;
    return new FloatAsDouble(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Double) != resolveTup(ex.valueType()))
      return null;
    return new DoubleAsFloat(ex);
  };
  implicits ~= delegate Expr(Expr ex) {
    auto dex = fastcast!(DoubleExpr)~ foldex(ex);
    if (!dex) return null;
    return new FloatExpr(cast(float) dex.d);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    auto ie = fastcast!(IntExpr)~ foldex(ex);
    if (!ie || ie.num > 65535 || ie.num < -32767) return null;
    return new IntLiteralAsShort(ie);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    auto ie = fastcast!(IntExpr)~ foldex(ex);
    if (!ie || ie.num > 255 || ie.num < -127) return null;
    return new IntLiteralAsByte(ie);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(SysInt) != resolveTup(ex.valueType()))
      return null;
    return new IntAsShort(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Short) != resolveTup(ex.valueType()))
      return null;
    return new ShortAsByte(ex);
  };
}

void loadFloatEx(Expr ex, AsmFile af) {
  if (auto lv = fastcast!(CValue)~ ex) {
    lv.emitLocation(af);
    af.popStack("%eax", nativePtrSize);
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
    af.popStack("%eax", nativePtrSize);
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
        af.popStack("%eax", 4);
        af.extendDivide("(%esp)", op == "/");
        af.sfree(4);
        if (op == "%") {
          af.pushStack("%edx", 4);
          af.nvm("%edx");
        } else {
          af.pushStack("%eax", 4);
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
          af.mmove4(op1, "%edx");
        } else {
          e1.emitAsm(af);
          af.popStack("%edx", 4);
        }
        string top = op;
        if (top == "*" && op2.startsWith("$")) {
          auto num = op2[1 .. $].atoi();
          if (num == 4) { top = "<<"; op2 = "$2"; }
        }
        
        auto asm_op = ([
          "+"[]: "addl"[], "-": "subl",
          "*": "imull", "/": "idivl",
          "xor": "xorl",
          "&": "andl", "|": "orl",
          "%": "imodl",
          "<<": "shl", ">>": "sar", ">>>": "shr"
        ])[top];
        
        if (op2.isRegister())
          af.popStack(op2, 4);
        
        if (asm_op == "sar" || asm_op == "shl" || asm_op == "%shr")
          if (op2 == "%ecx")
            op2 = "%cl"; // shl/r really want %cl.
        
        af.mathOp(asm_op, op2, "%edx");
        af.pushStack("%edx", 4);
        af.nvm("%edx");
      }
    }
  }
  static this() {
    foldopt ~= delegate Itr(Itr it) {
      auto aibe = fastcast!(AsmIntBinopExpr) (it);
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
        case "xor": return mkInt(ie1.num ^ ie2.num);
        default: assert(false, "can't opt/eval (int) "~aibe.op);
      }
    };
  }
}

class AsmIntUnaryExpr : Expr {
  Expr ex;
  string op;
  this(Expr e, string o) { ex = e; op = o; }
  mixin defaultIterate!(ex);
  override {
    AsmIntUnaryExpr dup() { return new AsmIntUnaryExpr(ex.dup, op); }
    IType valueType() { return ex.valueType(); }
    void emitAsm(AsmFile af) {
      if (op == "-") (new AsmIntBinopExpr(mkInt(0), ex, "-")).emitAsm(af);
      else if (op == "¬") {
        ex.emitAsm(af);
        af.popStack("%eax", 4);
        af.put("notl %eax");
        af.pushStack("%eax", 4);
      }
      else
      {
        logln("!! ", op, " ", ex);
        asm { int 3; }
      }
    }
  }
}

class AsmLongUnaryExpr : Expr {
  Expr ex;
  string op;
  this(Expr e, string o) { ex = e; op = o; }
  mixin defaultIterate!(ex);
  override {
    AsmLongUnaryExpr dup() { return new AsmLongUnaryExpr(ex.dup, op); }
    IType valueType() { return ex.valueType(); }
    void emitAsm(AsmFile af) {
      ex.emitAsm(af);
      if (op == "-") {
        af.put("negl 4(%esp)");
        af.put("notl (%esp)");
      } else if (op == "¬") {
        af.put("notl 4(%esp)");
        af.put("notl (%esp)");
      }
      else
      {
        logln("!! ", op, " ", ex);
        asm { int 3; }
      }
    }
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
        case "%": throw new Exception("Modulo not supported on floats. ");
      }
      af.storeFloat("(%esp)");
    }
  }
  static this() {
    foldopt ~= delegate Itr(Itr it) {
      auto afbe = fastcast!(AsmFloatBinopExpr) (it);
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
    foldopt ~= delegate Itr(Itr it) {
      auto adbe = fastcast!(AsmDoubleBinopExpr) (it);
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

BinopExpr delegate(Expr, Expr, string) mkLongExpr;

extern(C) IType resolveTup(IType, bool onlyIfChanged = false);

static this() {
  bool isInt(IType it) { return test(it == Single!(SysInt)); }
  bool isFloat(IType it) { return test(it == Single!(Float)); }
  bool isDouble(IType it) { return test(it == Single!(Double)); }
  bool isLong(IType it) { return test(it == Single!(Long)); }
  bool isPointer(IType it) { return test(fastcast!(Pointer)~ it); }
  Expr handleIntMath(string op, Expr ex1, Expr ex2) {
    if (!gotImplicitCast(ex1, &isInt) || !gotImplicitCast(ex2, &isInt))
      return null;
    return new AsmIntBinopExpr(ex1, ex2, op);
  }
  Expr handleIntUnary(string op, Expr ex) {
    if (!gotImplicitCast(ex, &isInt))
      return null;
    return new AsmIntUnaryExpr(ex, op);
  }
  Expr handleLongUnary(string op, Expr ex) {
    if (!gotImplicitCast(ex, &isLong))
      return null;
    return new AsmLongUnaryExpr(ex, op);
  }
  Expr handleNeg(Expr ex) {
    return lookupOp("-", mkInt(0), ex);
  }
  Expr handlePointerMath(string op, Expr ex1, Expr ex2) {
    auto ex22 = ex2;
    if (fastcast!(Pointer) (resolveTup(ex22.valueType()))) {
      if (op == "-") {
        return null; // wut
      }
      swap(ex1, ex2);
    }
    if (fastcast!(Pointer) (resolveTup(ex1.valueType()))) {
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
    if (Single!(Double) != resolveTup(ex1.valueType())
     && Single!(Double) != resolveTup(ex2.valueType()))
      return null;
    if (!gotImplicitCast(ex1, &isDouble) || !gotImplicitCast(ex2, &isDouble))
      return null;
    
    return new AsmDoubleBinopExpr(ex1, ex2, op);
  }
  Expr handleLongMath(string op, Expr ex1, Expr ex2) {
    if (Single!(Long) != resolveTup(ex1.valueType())
     && Single!(Long) != resolveTup(ex2.valueType()))
      return null;
    if (!gotImplicitCast(ex1, &isLong) || !gotImplicitCast(ex2, &isLong))
      return null;
    
    return mkLongExpr(ex1, ex2, op);
  }
  void defineOps(Expr delegate(string op, Expr, Expr) dg, bool reduced = false) {
    string[] ops;
    if (reduced) ops = ["+", "-"]; // pointer math
    else ops = ["+", "-", "&", "|", "*", "/", "%", "<<", ">>", ">>>", "xor"];
    foreach (op; ops)
      defineOp(op, op /apply/ dg);
  }
  defineOp("¬", "¬" /apply/ &handleIntUnary);
  defineOp("¬", "¬" /apply/ &handleLongUnary);
  defineOp("-", &handleNeg);
  defineOps(&handleIntMath);
  defineOps(&handleFloatMath);
  defineOps(&handleDoubleMath);
  defineOps(&handleLongMath);
  defineOps(&handlePointerMath, true);
}

static this() { parsecon.addPrecedence("tree.expr.arith", "12"); }

const oplist = [
  "+"[], "-", "*", "/",
  "xor", "|", "&", "%",
  "<<", ">>", "^", "x"
];

const oplevel = [
  0, 1, 2, 2,
  3, 4, 5, 6,
  7, 7, 8, 8
];

const lvcount = 9;

Object gotMathExpr(ref string text, ParseCb cont, ParseCb rest) {
  Object _curOp;
  auto t2 = text;
  if (!cont(t2, &_curOp)) return null;
  Expr curOp = fastcast!(Expr) (_curOp);
  if (!curOp) return null;
  curOp = forcedConvert(curOp);
  foreach (op; oplist) {
    auto t3 = t2;
    if (t3.accept(op) && t3.accept("=")) {
      Expr src;
      if (!rest(t3, "tree.expr", &src))
        t3.failparse("Could not find source operand for assignment! ");
      auto res = lookupOp(op~"=", curOp, src);
      if (res) text = t3;
      return fastcast!(Object) (res);
    }
  }
  Expr recurse(Expr op, int depth) {
    if (depth == lvcount) return op;
    op = recurse(op, depth + 1);
    retry:
    string opName; int _i;
    // this will all be unrolled and optimized out
    string t3;
    foreach (i, bogus; Repeat!(void, lvcount))
      if (i == depth)
        foreach (k, bogus2; Repeat!(void, oplevel.length))
          if (oplevel[k] == i) {
            t3 = t2;
            opName = oplist[k]; _i = i;
            bool accepted = t3.accept(opName);
            if (t3.startsWith(opName)) accepted = false;
            if (accepted) {
              goto accepted_handler;
            }
          }
    return op;
    // shared code for all the cases - simplifies asm output
  accepted_handler:
    Expr nextOp;
    if (!cont(t3, &nextOp)) {
      // may be part of a magnitude expr
      if (opName == "|") return op;
      // may be start of a heredoc
      if (opName == "<<") return op;
      t3.failparse("Could not find second operand for ", opName);
    }
    nextOp = forcedConvert(nextOp);
    t2 = t3;
    try op = lookupOp(opName, op, recurse(nextOp, _i + 1));
    catch (Exception ex) t2.failparse(ex);
    goto retry;
  }
  while (true) {
    curOp = recurse(curOp, 0);
    if (!t2.accept("#")) break;
    withPropcfgFn((bool withTuple, bool withCall) {
      if (auto res = getPropertiesFn(
          t2, fastcast!(Object) (curOp), withTuple, withCall, cont, rest
        )
      )
        if (auto res2 = fastcast!(Expr) (res))
          curOp = res2;
    });
  }
  text = t2;
  return fastcast!(Object) (curOp);
}

import ast.pointer, ast.opers, tools.base: swap;
mixin DefaultParser!(gotMathExpr, "tree.expr.arith.ops", "31");

Object gotPrefixExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool isNeg;
  if (t2.accept("-")) { isNeg = true; }
  else {
    if (!t2.accept("¬")) return null;
  }
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Found no expression for negation");
  text = t2;
  string op;
  if (isNeg) op = "-";
  else op = "¬";
  try {
    if (auto lop = lookupOp(op, true, ex))
      return fastcast!(Object)~ lop;
  } catch (Exception ex) {
    t2.failparse(ex);
  }
  t2.failparse("Found no lookup match for negation/inversion of ", ex.valueType());
}
mixin DefaultParser!(gotPrefixExpr, "tree.expr.prefix", "213");

class FSqrtExpr : Expr {
  Expr sup;
  this(Expr ex) { sup = ex; }
  mixin defaultIterate!(sup);
  override {
    IType valueType() { return Single!(Float); }
    FSqrtExpr dup() { return new FSqrtExpr(sup.dup); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"));
      sup.emitAsm(af);
      af.loadFloat("(%esp)");
      af.floatMath("fsqrt", false);
      af.storeFloat("(%esp)");
    }
  }
}

class SSESqrtExpr : Expr {
  Expr sup;
  this(Expr ex) { sup = ex; }
  mixin defaultIterate!(sup);
  override {
    IType valueType() { return Single!(Float); }
    FSqrtExpr dup() { return new FSqrtExpr(sup.dup); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"));
      sup.emitAsm(af);
      af.SSEOp("movd", "(%esp)", "%xmm0", true /* ignore stack alignment */);
      af.SSEOp("sqrtss", "%xmm0", "%xmm0");
      af.SSEOp("movd", "%xmm0", "(%esp)", true);
    }
  }
}

import ast.modules;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto fc = fastcast!(FunCall) (it);
    if (!fc) return null;
    bool isSqrtMath, isSqrtfSysmod;
    auto sqrmod = fastcast!(Module) (fc.fun.sup);
    if (fc.fun.name == "sqrt" /or/ "[wrap]sqrt") {
      if (sqrmod && sqrmod.name == "std.math") isSqrtMath = true;
    }
    if (fc.fun.name == "sqrtf" /or/ "[wrap]sqrtf") {
      if (sqrmod && sysmod && sqrmod is sysmod) isSqrtfSysmod = true;
    }
    if (!isSqrtMath && !isSqrtfSysmod) return null;
    auto arg = foldex(fc.getParams()[0]);
    // return new FSqrtExpr(arg);
    return new SSESqrtExpr(arg);
  };
}
