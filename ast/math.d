module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and, or, find, todg;

Object function(ref string, Object, bool, bool, ParseCb, ParseCb, bool rawmode = false) getPropertiesFn;
void function(void delegate(bool, bool)) withPropcfgFn;

class IntAsFloat : Expr {
  Expr i;
  this(Expr i) { this.i = i; assert(Single!(SysInt) == i.valueType()); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(i);
  override {
    string toString() { return Format("float("[], i, ")"[]); }
    IType valueType() { return Single!(Float); }
    void emitLLVM(LLVMFile lf) {
      todo("IntAsFloat::emitLLVM");
      /*mixin(mustOffset("4"[]));
      i.emitLLVM(lf);
      lf.loadIntAsFloat("(%esp)"[]);
      lf.storeFloat("(%esp)"[]);*/
    }
  }
}

class LongAsDouble : Expr {
  Expr l;
  this(Expr l) { this.l = l; assert(Single!(Long) == l.valueType()); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(l);
  override {
    string toString() { return Format("double("[], l, ")"[]); }
    IType valueType() { return Single!(Double); }
    void emitLLVM(LLVMFile lf) {
      todo("LongAsDouble::emitLLVM");
      /*mixin(mustOffset("8"[]));
      l.emitLLVM(lf);
      lf.loadLongAsFloat("(%esp)"[]);
      lf.storeDouble("(%esp)"[]);*/
    }
  }
}

class LongAsInt : Expr {
  Expr l;
  this(Expr l) { this.l = l; assert(Single!(Long) == l.valueType()); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(l);
  override {
    string toString() { return Format("int(", l, ")"); }
    IType valueType() { return Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      todo("LongAsInt::emitLLVM");
      /*mixin(mustOffset("4"[]));
      l.emitLLVM(lf);
      // overwrite high int with low
      lf.popStack("4(%esp)", 4);*/
    }
  }
}

import ast.casting, ast.fold, ast.literals, ast.fun;
extern(C) float sqrtf(float);
static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto iaf = fastcast!(IntAsFloat) (it)) {
      if (auto ie = fastcast!(IntExpr) (iaf.i)) {
        return fastalloc!(FloatExpr)(ie.num);
      }
    }
    if (auto lad = fastcast!(LongAsDouble) (it)) {
      if (auto ial = fastcast!(IntAsLong) (lad.l)) {
        if (auto ie = fastcast!(IntExpr) (ial.i)) {
          return fastalloc!(DoubleExpr)(ie.num);
        }
      }
    }
    if (auto fad = fastcast!(FloatAsDouble) (it)) {
      if (auto fe = fastcast!(FloatExpr) (fad.f)) {
        return fastalloc!(DoubleExpr) (fe.f);
      }
    }
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto fc = fastcast!(FunCall) (it)) {
      if (fc.fun.extern_c && fc.fun.name == "sqrtf"[]) {
        assert(fc.params.length == 1);
        auto fe = fc.params[0];
        if (!gotImplicitCast(fe, (Expr ex) { opt(ex); return test(fastcast!(FloatExpr) (ex)); }))
          return null;
        opt(fe);
        return fastalloc!(FloatExpr)(sqrtf((fastcast!(FloatExpr) (fe)).f));
      }
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != resolveType(ex.valueType())) return null;
    return fastalloc!(IntAsFloat)(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Long) != resolveType(ex.valueType())) return null;
    return fastalloc!(LongAsDouble)(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Long) != resolveType(ex.valueType())) return null;
    return fastalloc!(LongAsInt)(ex);
  };
}

class IntAsLong : Expr {
  Expr i;
  this(Expr i) { this.i = i; assert(Single!(SysInt) == i.valueType()); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(i);
  override {
    string toString() { return Format("long("[], i, ")"[]); }
    IType valueType() { return Single!(Long); }
    void emitLLVM(LLVMFile lf) {
      todo("IntAsLong::emitLLVM");
      /*mixin(mustOffset("8"[]));
      i.emitLLVM(lf);
      // duplicate
      lf.pushStack("(%esp)", 4);
      // sign extend high int
      lf.mathOp("sarl", "$31", "4(%esp)");*/
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    return fastalloc!(IntAsLong)(ex);
  };
}

class FPAsInt : Expr {
  Expr fp;
  bool dbl, lng;
  this(Expr fp, bool dbl = false, bool lng = false) {
    this.fp = fp;
    this.dbl = dbl;
    this.lng = lng;
    if (dbl)
      assert(Single!(Double) == fp.valueType());
    else
      assert(Single!(Float) == fp.valueType());
  }
  private this() { }
  mixin DefaultDup;
  mixin defaultIterate!(fp);
  override {
    string toString() { if (lng) return Format("long:"[], fp); else return Format("int:"[], fp); }
    IType valueType() { return lng?Single!(Long):Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      todo("FPAsInt::emitLLVM");
      /*if (lng) {
        mixin(mustOffset("8"[]));
        fp.emitLLVM(lf);
        if (dbl) lf.loadDouble("(%esp)"[]);
        else lf.loadFloat("(%esp)"[]);
        if (!dbl) lf.salloc(4);
        lf.storeFPAsLong("(%esp)"[]);
      } else {
        mixin(mustOffset("4"[]));
        fp.emitLLVM(lf);
        if (dbl) lf.loadDouble("(%esp)"[]);
        else lf.loadFloat("(%esp)"[]);
        if (dbl) lf.sfree(4);
        lf.storeFPAsInt("(%esp)"[]);
      }*/
    }
  }
}

Expr floatToInt(Expr ex, IType) {
  auto ex2 = ex;
  // something that casts to float, but not int by itself.
  if (gotImplicitCast(ex2, Single!(SysInt), (IType it) { return test(Single!(SysInt) == it); })
   ||!gotImplicitCast(ex, Single!(Float), (IType it) { return test(Single!(Float) == it); }))
    return null;
  
  return fastalloc!(FPAsInt)(ex);
}

Expr doubleToInt(Expr ex, IType) {
  auto ex2 = ex;
  if (gotImplicitCast(ex2, Single!(SysInt), (IType it) { return test(Single!(SysInt) == it); })
   ||!gotImplicitCast(ex, Single!(Double), (IType it) { return test(Single!(Double) == it); }))
    return null;
  
  return fastalloc!(FPAsInt)(ex, true);
}

Expr doubleToLong(Expr ex, IType) {
  auto ex2 = ex;
  if (gotImplicitCast(ex2, Single!(Long), (IType it) { return test(Single!(Long) == it); })
   ||!gotImplicitCast(ex, Single!(Double), (IType it) { return test(Single!(Double) == it); }))
    return null;
  
  return fastalloc!(FPAsInt)(ex, true, true /* long */);
}

static this() {
  converts ~= &floatToInt /todg;
  converts ~= &doubleToInt /todg;
  converts ~= &doubleToLong /todg;
}

class FloatAsDouble : Expr {
  Expr f;
  this(Expr f) { this.f = f; assert(Single!(Float) == f.valueType()); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(f);
  override {
    IType valueType() { return Single!(Double); }
    void emitLLVM(LLVMFile lf) {
      todo("FloatAsDouble::emitLLVM");
      /*mixin(mustOffset("8"[]));
      f.emitLLVM(lf);
      lf.loadFloat("(%esp)"[]);
      lf.salloc(4);
      lf.storeDouble("(%esp)"[]);*/
    }
  }
}

class DoubleAsFloat : Expr {
  Expr d;
  this(Expr d) {
    this.d = d;
    if (resolveTup(d.valueType()) != Single!(Double)) fail;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(d);
  override {
    IType valueType() { return Single!(Float); }
    string toString() { return Format("float:"[], d); }
    void emitLLVM(LLVMFile lf) {
      todo("DoubleAsFloat::emitLLVM");
      /*mixin(mustOffset("4"[]));
      d.emitLLVM(lf);
      lf.loadDouble("(%esp)"[]);
      lf.sfree(4);
      lf.storeFloat("(%esp)"[]);*/
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
    string toString() { return Format("short:"[], ie); }
    void emitLLVM(LLVMFile lf) {
      todo("IntLiteralAsShort::emitLLVM");
      /*mixin(mustOffset("2"[]));
      if (isARM) {
        lf.salloc(2);
        ie.emitLLVM(lf);
        lf.popStack("r0"[], 4);
        lf.mmove2("r0"[], "[sp]"[]);
      } else {
        lf.mmove2(Format("$"[], ie.num), "%ax"[]);
        lf.pushStack("%ax"[], 2);
      }*/
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
    string toString() { return Format("byte:"[], ie); }
    void emitLLVM(LLVMFile lf) {
      todo("IntLiteralAsByte::emitLLVM");
      /*mixin(mustOffset("1"[]));
      lf.salloc(1);
      if (isARM) {
        lf.mmove4(lf.number(ie.num), "r0"[]);
        lf.mmove1("r0"[], "[sp]"[]);
      } else {
        lf.mmove1(lf.number(ie.num), "(%esp)"[]);
      }*/
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
    string toString() { return Format("short:"[], ex); }
    void emitLLVM(LLVMFile lf) {
      todo("IntAsShort::emitLLVM");
      /*mixin(mustOffset("2"[]));
      ex.emitLLVM(lf);
      if (isARM) {
        lf.popStack("r0"[], 4);
        logln("TODO: proper int to short"[]);
        lf.salloc(2);
        lf.mmove2("r0"[], "[sp]"[]);
        return;
      }
      lf.popStack("%eax"[], 4);
      lf.mmove4("%eax"[], "%ebx"[]);
      lf.mathOp("shrl"[], "$16"[], "%ebx"[]); // move eah into eal
      lf.mathOp("andw"[], "$32768"[], "%bx"[]); // select high bit
      lf.mathOp("andw"[], "$32767"[], "%ax"[]); // mask out high bit
      lf.mathOp("orw"[], "%bx"[], "%ax"[]); // copy bit
      lf.pushStack("%ax"[], 2);*/
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
    IType valueType() { return Single!(Byte); }
    void emitLLVM(LLVMFile lf) {
      todo("ShortAsByte::emitLLVM");
      /*mixin(mustOffset("1"[]));
      ex.emitLLVM(lf);
      if (isARM) {
        lf.mmove2("[sp]"[], "r0"[]);
        lf.sfree(1);
        lf.mmove1("r0"[], "[sp]"[]);
        return;
      }
      lf.popStack("%ax"[], 2);
      lf.pushStack("%al"[], 1);*/
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(Float) != ex.valueType()) return null;
    return fastalloc!(FloatAsDouble)(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Double) != resolveTup(ex.valueType()))
      return null;
    return fastalloc!(DoubleAsFloat)(ex);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(Double) != ex.valueType()) return null;
    opt(ex);
    auto dex = fastcast!(DoubleExpr) (ex);
    if (!dex) return null;
    return fastalloc!(FloatExpr)(cast(float) dex.d);
  };
  implicits ~= delegate Expr(Expr ex, IType desired) {
    if (Single!(SysInt) != ex.valueType()) return null;
    opt(ex);
    auto ie = fastcast!(IntExpr) (ex);
    if (!ie) return null;
    if (ie.num > 65535 || ie.num < -32767) {
      if (desired && Single!(Short) == desired)
        throw new Exception(Format(ie.num, " does not fit into short"));
      return null;
    }
    return fastalloc!(IntLiteralAsShort)(ie);
  };
  implicits ~= delegate void(Expr ex, IType desired, void delegate(Expr) dg) {
    if (Single!(SysInt) != ex.valueType()) return;
    opt(ex);
    auto ie = fastcast!(IntExpr) (ex);
    if (!ie) return;
    if (ie.num > 255 || ie.num < -127) {
      if (desired && Single!(Byte) == desired)
        throw new Exception(Format(ie.num, " does not fit into byte"));
      return;
    }
    auto litbyte = fastalloc!(IntLiteralAsByte)(ie);
    dg(litbyte);
    dg(reinterpret_cast(Single!(UByte), litbyte));
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(SysInt) != resolveTup(ex.valueType()))
      return null;
    return fastalloc!(IntAsShort)(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Short) != resolveTup(ex.valueType()))
      return null;
    return fastalloc!(ShortAsByte)(ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(Byte) != resolveTup(ex.valueType()))
      return null;
    return reinterpret_cast(Single!(UByte), ex);
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(SysInt) != resolveTup(ex.valueType()))
      return null;
    return fastalloc!(ShortAsByte)(fastalloc!(IntAsShort)(ex));
  };
  converts ~= delegate Expr(Expr ex, IType it) {
    if (Single!(SysInt) != resolveTup(ex.valueType()))
      return null;
    return reinterpret_cast(Single!(UByte),
      fastalloc!(ShortAsByte)(fastalloc!(IntAsShort)(ex)));
  };
}

void loadFloatEx(Expr ex, LLVMFile lf) {
  todo("loadFloatEx");
  /*if (auto lv = fastcast!(CValue)~ ex) {
    lv.emitLocation(lf);
    lf.popStack("%eax"[], nativePtrSize);
    lf.loadFloat("(%eax)"[]);
    lf.nvm("%eax"[]);
  } else {
    int toFree = 4 + alignStackFor(ex.valueType(), lf);
    ex.emitLLVM(lf);
    lf.loadFloat("(%esp)"[]);
    lf.sfree(toFree);
  }*/
}

void loadDoubleEx(Expr ex, LLVMFile lf) {
  todo("loadDoubleEx");
  /*if (auto cv = fastcast!(CValue)~ ex) {
    cv.emitLocation(lf);
    lf.popStack("%eax"[], nativePtrSize);
    lf.loadDouble("(%eax)"[]);
    lf.nvm("%eax"[]);
  } else {
    ex.emitLLVM(lf);
    lf.loadDouble("(%esp)"[]);
    lf.sfree(8);
  }*/
}

abstract class BinopExpr : Expr, HasInfo {
  Expr e1, e2;
  string op;
  this(Expr e1, Expr e2, string op) {
    if (!e1 || !e2)
      fail;
    // opt(e1);
    // opt(e2);
    this.e1 = e1;
    this.e2 = e2;
    this.op = op;
  }
  protected this() {}
  mixin defaultIterate!(e1, e2);
  override {
    string toString() {
      return Format("("[], e1, " "[], op, " "[], e2, ")"[]);
    }
    string getInfo() { return op; }
    IType valueType() { // TODO: merge e1, e2
      auto e1vt = e1.valueType();
      if (e1vt != e2.valueType()) {
        logln("Divergent types: "[], e1.valueType(), " and "[], e2.valueType());
        fail;
      }
      return e1vt;
    }
    abstract BinopExpr dup();
    abstract void emitLLVM(LLVMFile lf);
  }
}

class AsmIntBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) {
    super(e1, e2, op);
  }
  private this() { super(); }
  AsmIntBinopExpr dup() { return fastalloc!(AsmIntBinopExpr)(e1.dup, e2.dup, op); }
  override {
    void emitLLVM(LLVMFile lf) {
      todo("AsmIntBinopExpr::emitLLVM");
      /*assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      if (isARM) {
        e2.emitLLVM(lf);
        e1.emitLLVM(lf);
        lf.popStack("r1"[], 4);
        lf.popStack("r0"[], 4);
        string asmop;
        if (op == "+"[]) asmop = "add";
        if (op == "-"[]) asmop = "sub";
        if (op == "*"[]) asmop = "mul";
        if (op == "&"[]) asmop = "and";
        if (op == "|"[]) asmop = "orr";
        if (op == "<<"[]) asmop = "lsl";
        if (op == ">>"[]) asmop = "lsr";
        if (op == "xor"[]) asmop = "eor";
        
        if (!asmop) { logln(op); fail; }
        lf.mathOp(asmop, "r0"[], "r1"[], "r0"[]);
        lf.pushStack("r0"[], 4);
        return;
      }
      if (op == "/" || op == "%"[]) {
        e2.emitLLVM(lf);
        e1.emitLLVM(lf);
        lf.popStack("%eax"[], 4);
        lf.extendDivide("(%esp)"[], op == "/"[]);
        lf.sfree(4);
        if (op == "%"[]) {
          lf.pushStack("%edx"[], 4);
          lf.nvm("%edx"[]);
        } else {
          lf.pushStack("%eax"[], 4);
          lf.nvm("%eax"[]);
        }
      } else {
        string op1, op2;
        if (auto c2 = fastcast!(IntExpr) (e2)) {
          op2 = Format("$"[], c2.num);
        } else {
          op2 = "%ecx";
          e2.emitLLVM(lf);
        }
        if (auto c1 = fastcast!(IntExpr) (e1)) {
          op1 = Format("$"[], c1.num);
          lf.mmove4(op1, "%edx"[]);
        } else {
          e1.emitLLVM(lf);
          lf.popStack("%edx"[], 4);
        }
        string top = op;
        if (top == "*" && op2.startsWith("$"[])) {
          auto num = op2[1 .. $].my_atoi();
          if (num == 4) { top = "<<"; op2 = "$2"; }
        }
        
        string asm_op;
        switch (top) {
          case "+": asm_op = "addl"; break;
          case "-": asm_op = "subl"; break;
          case "*": asm_op = "imull"; break;
          case "/": asm_op = "idivl"; break;
          case "xor": asm_op = "xorl"; break;
          case "&": asm_op = "andl"; break;
          case "|": asm_op = "orl"; break;
          case "%": asm_op = "imodl"; break;
          case "<<": asm_op = "shl"; break;
          case ">>": asm_op = "sar"; break;
          case ">>>": asm_op = "shr"; break;
          default: fail;
        }
        
        if (op2.isRegister())
          lf.popStack(op2, 4);
        
        if (asm_op == "sar" || asm_op == "shl" || asm_op == "%shr"[])
          if (op2 == "%ecx"[])
            op2 = "%cl"; // shl/r really want %cl.
        
        lf.mathOp(asm_op, op2, "%edx"[]);
        lf.pushStack("%edx"[], 4);
        lf.nvm("%edx"[]);
      }*/
    }
  }
  static this() {
    foldopt ~= delegate Itr(Itr it) {
      auto aibe = fastcast!(AsmIntBinopExpr) (it);
      if (!aibe) return null;
      auto ie1 = fastcast!(IntExpr) (aibe.e1);
      if (!ie1) return null;
      auto ie2 = fastcast!(IntExpr) (aibe.e2);
      if (!ie2) return null;
      void checkZero(string kind, int num) {
        if (!num) throw new Exception(Format("Could not compute "~kind~": division by zero"[]));
      }
      switch (aibe.op) {
        case "+": return mkInt(ie1.num + ie2.num);
        case "-": return mkInt(ie1.num - ie2.num);
        case "*": return mkInt(ie1.num * ie2.num);
        case "/": checkZero("division"[], ie2.num); return mkInt(ie1.num / ie2.num);
        case "%": checkZero("modulo"[], ie2.num); return mkInt(ie1.num % ie2.num);
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
    AsmIntUnaryExpr dup() { return fastalloc!(AsmIntUnaryExpr)(ex.dup, op); }
    IType valueType() { return ex.valueType(); }
    void emitLLVM(LLVMFile lf) {
      todo("AsmIntUnaryExpr::emitLLVM");
      /*if (op == "-"[]) (fastalloc!(AsmIntBinopExpr)(mkInt(0), ex, "-"[])).emitLLVM(lf);
      else if (op == "¬"[]) {
        ex.emitLLVM(lf);
        lf.popStack("%eax"[], 4);
        lf.put("notl %eax"[]);
        lf.pushStack("%eax"[], 4);
      }
      else
      {
        logln("!! "[], op, " "[], ex);
        fail;
      }*/
    }
  }
}

class AsmLongUnaryExpr : Expr {
  Expr ex;
  string op;
  this(Expr e, string o) { ex = e; op = o; }
  mixin defaultIterate!(ex);
  override {
    AsmLongUnaryExpr dup() { return fastalloc!(AsmLongUnaryExpr)(ex.dup, op); }
    IType valueType() { return ex.valueType(); }
    void emitLLVM(LLVMFile lf) {
      todo("AsmLongUnaryExpr::emitLLVM");
      /*ex.emitLLVM(lf);
      if (op == "-"[]) {
        lf.put("negl 4(%esp)"[]);
        lf.put("notl (%esp)"[]);
      } else if (op == "¬"[]) {
        lf.put("notl 4(%esp)"[]);
        lf.put("notl (%esp)"[]);
      }
      else
      {
        logln("!! "[], op, " "[], ex);
        fail;
      }*/
    }
  }
}

class AsmFloatBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  override {
    AsmFloatBinopExpr dup() { return fastalloc!(AsmFloatBinopExpr)(e1.dup, e2.dup, op); }
    void emitLLVM(LLVMFile lf) {
      todo("AsmFloatBinopExpr::emitLLVM");
      /*assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      // TODO: belongs in optimizer
      bool commutative = op == "+" || op == "*";
      if (commutative) {
        // hackaround for circular dep avoidance
        if ((fastcast!(Object)~ e2).classinfo.name.find("Variable"[]) != -1 || fastcast!(FloatExpr)~ e2 || fastcast!(IntAsFloat)~ e2)
          swap(e1, e2); // try to eval simpler expr last
      }
      loadFloatEx(e2, lf);
      loadFloatEx(e1, lf);
      lf.salloc(4);
      switch (op) {
        case "+": lf.floatMath("fadd"[]); break;
        case "-": lf.floatMath("fsub"[]); break;
        case "*": lf.floatMath("fmul"[]); break;
        case "/": lf.floatMath("fdiv"[]); break;
        case "%": // taken from glibc
          lf.floatStackDepth --;
          lf.put("1: fprem1"[]); // ieee-correct remainder
          lf.put("fstsw %ax"[]); // sets parity if unfinished
          lf.put("sahf"[]);
          lf.put("jp 1b"[]);     // in that case, rerun it
          lf.put("fstp %st(1)"[]); // pop unneeded
          break;
      }
      lf.storeFloat("(%esp)"[]);*/
    }
  }
  static this() {
    foldopt ~= delegate Itr(Itr it) {
      auto afbe = fastcast!(AsmFloatBinopExpr) (it);
      if (!afbe) return null;
      auto
        e1 = afbe.e1, fe1 = fastcast!(FloatExpr) (e1),
        e2 = afbe.e2, fe2 = fastcast!(FloatExpr) (e2);
      if (!fe1 || !fe2) {
        if (afbe.op == "/" && fe2) { // optimize constant division into multiplication
          auto val = fe2.f;
          if (val == 0) throw new Exception("division by zero");
          return fastalloc!(AsmFloatBinopExpr)(e1, fastalloc!(FloatExpr)(1f / val), "*");
        }
        if (e1 !is afbe.e1 || e2 !is afbe.e2)
          return fastalloc!(AsmFloatBinopExpr)(e1, e2, afbe.op);
        return null;
      }
      switch (afbe.op) {
        case "+": return fastalloc!(FloatExpr)(fe1.f + fe2.f);
        case "-": return fastalloc!(FloatExpr)(fe1.f - fe2.f);
        case "*": return fastalloc!(FloatExpr)(fe1.f * fe2.f);
        case "/": return fastalloc!(FloatExpr)(fe1.f / fe2.f);
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
    AsmDoubleBinopExpr dup() { return fastalloc!(AsmDoubleBinopExpr)(e1.dup, e2.dup, op); }
    void emitLLVM(LLVMFile lf) {
      todo("AsmDoubleBinopExpr::emitLLVM");
      /*assert(e1.valueType().size == 8);
      assert(e2.valueType().size == 8);
      loadDoubleEx(e2, lf);
      loadDoubleEx(e1, lf);
      lf.salloc(8);
      switch (op) {
        case "+": lf.floatMath("fadd"[]); break;
        case "-": lf.floatMath("fsub"[]); break;
        case "*": lf.floatMath("fmul"[]); break;
        case "/": lf.floatMath("fdiv"[]); break;
        case "%": assert(false, "Modulo not supported on floats. "[]);
      }
      lf.storeDouble("(%esp)"[]);*/
    }
  }
  static this() {
    foldopt ~= delegate Itr(Itr it) {
      auto adbe = fastcast!(AsmDoubleBinopExpr) (it);
      if (!adbe) return null;
      auto
        e1 = adbe.e1, de1 = fastcast!(DoubleExpr)~ e1,
        e2 = adbe.e2, de2 = fastcast!(DoubleExpr)~ e2;
      if (!de1 || !de2) {
        if (adbe.op == "/" && de2) { // see above
          auto val = de2.d;
          if (val == 0) throw new Exception("division by zero");
          return fastalloc!(AsmDoubleBinopExpr)(e1, fastalloc!(DoubleExpr)(1.0 / val), "*");
        }
        if (e1 !is adbe.e1 || e2 !is adbe.e2)
          return fastalloc!(AsmDoubleBinopExpr)(e1, e2, adbe.op);
        return null;
      }
      switch (adbe.op) {
        case "+": return fastalloc!(DoubleExpr)(de1.d + de2.d);
        case "-": return fastalloc!(DoubleExpr)(de1.d - de2.d);
        case "*": return fastalloc!(DoubleExpr)(de1.d * de2.d);
        case "/": return fastalloc!(DoubleExpr)(de1.d / de2.d);
        default: assert(false, "can't opt/eval (double) "~adbe.op);
      }
      return null;
    };
  }
}

BinopExpr delegate(Expr, Expr, string) mkLongExpr;

extern(C) IType resolveTup(IType, bool onlyIfChanged = false);

static this() { addPrecedence("tree.expr.arith"[], "12"[]); }

const oplist = [
  "+"[], "-"[], "*"[], "/"[],
  "xor"[], "|"[], "&"[], "%"[],
  "<<"[], ">>>"[], ">>"[], "^"[], "x"
];

const oplevel = [
  1, 1, 2, 2,
  3, 4, 5, 6,
  7, 7, 7, 8, 8
];

const lvcount = 9;

TLS!(string) octoless_marker;
static this() { New(octoless_marker); }

Object gotMathExpr(ref string text, ParseCb cont, ParseCb rest) {
  Object _curOp;
  auto t2 = text;
  if (!cont(t2, &_curOp)) return null;
  Expr curOp = fastcast!(Expr) (_curOp);
  if (!curOp) return null;
  curOp = forcedConvert(curOp);
  bool octoless;
  if (*octoless_marker.ptr() is text)
    octoless = true;
  foreach (op; oplist) {
    if (op == "x"[]) continue; // what, no, bad idea
    auto t3 = t2;
    if (t3.accept(op) && t3.accept("="[])) {
      Expr src;
      if (!rest(t3, "tree.expr"[], &src))
        t3.failparse("Could not find source operand for assignment! "[]);
      try {
        auto res = lookupOp(op~"="[], curOp, src);
        if (res) text = t3;
        return fastcast!(Object) (res);
      } catch (Exception ex) {
        text.failparse(ex);
      }
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
            if (opName == "x"[]) accepted &= !t3.startsWith("-"[]); // x-something is an identifier!
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
      if (opName == "|"[]) return op;
      // may be start of a heredoc
      if (opName == "<<"[]) return op;
      if (*lenient.ptr()) return null;
      t3.failparse("Could not find second operand for "[], opName);
    }
    nextOp = forcedConvert(nextOp);
    auto backupt2 = t2;
    t2 = t3;
    try {
      auto recursed = recurse(nextOp, _i + 1);
      auto op2 = lookupOp(opName, true, op, recursed);
      if (!op2) {
	if( recursed)
	  backupt2.setError("Undefined operation: ", op.valueType(), " ", opName, " ", recursed.valueType());
	t2 = backupt2;
	return null;
      }
      op = op2;
    } catch (Exception ex) t2.failparse(ex);
    goto retry;
  }
  bool correctlyAteOctothorpe;
  string t2backup;
  while (true) {
    auto newOp = recurse(curOp, 0);
    correctlyAteOctothorpe |= newOp !is curOp;
    curOp = newOp;
    
    if (t2backup && !correctlyAteOctothorpe) {
      // nothing matched, back out
      t2 = t2backup;
      break;
    }
    
    correctlyAteOctothorpe = false;
    t2backup = t2;
    if (octoless || !t2.accept("#"[])) break;
    
    withPropcfgFn((bool withTuple, bool withCall) {
      if (auto res = getPropertiesFn(
          t2, fastcast!(Object) (curOp), withTuple, withCall, cont, rest
        )
      )
        if (auto res2 = fastcast!(Expr) (res)) {
          correctlyAteOctothorpe = true;
          curOp = res2;
        }
    });
  }
  text = t2;
  return fastcast!(Object) (curOp);
}

import ast.pointer, ast.opers, tools.base: swap;
mixin DefaultParser!(gotMathExpr, "tree.expr.arith.ops"[], "31"[]);

Object gotPrefixExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool isNeg;
  if (t2.accept("-"[])) { isNeg = true; }
  else {
    if (!t2.accept("¬")/* && !t2.accept("neg"[])*/) return null;
  }
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith"[], &ex)) {
    if (*lenient.ptr()) return null; // maybe in a C-expr?
    t2.failparse("Found no expression for negation"[]);
  }
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
  t2.failparse("Found no lookup match for negation/inversion of "[], ex.valueType());
}
mixin DefaultParser!(gotPrefixExpr, "tree.expr.prefix"[], "213"[]);

class FSqrtExpr : Expr {
  Expr sup;
  this(Expr ex) { sup = ex; }
  mixin defaultIterate!(sup);
  override {
    IType valueType() { return Single!(Float); }
    FSqrtExpr dup() { return fastalloc!(FSqrtExpr)(sup.dup); }
    void emitLLVM(LLVMFile lf) {
      todo("FSqrtExpr::emitLLVM");
      /*mixin(mustOffset("4"[]));
      sup.emitLLVM(lf);
      lf.loadFloat("(%esp)"[]);
      lf.floatMath("fsqrt"[], false);
      lf.storeFloat("(%esp)"[]);*/
    }
  }
}

class FSinExpr : Expr {
  Expr sup;
  this(Expr ex) { sup = ex; }
  mixin defaultIterate!(sup);
  override {
    IType valueType() { return Single!(Float); }
    FSinExpr dup() { return fastalloc!(FSinExpr)(sup.dup); }
    void emitLLVM(LLVMFile lf) {
      todo("FSinExpr::emitLLVM");
      /*mixin(mustOffset("4"[]));
      sup.emitLLVM(lf);
      lf.loadFloat("(%esp)"[]);
      lf.fpuOp("fsin"[]);
      lf.storeFloat("(%esp)"[]);*/
    }
  }
}

class FAbsFExpr : Expr {
  Expr sup;
  this(Expr ex) { sup = ex; }
  mixin defaultIterate!(sup);
  override {
    IType valueType() { return Single!(Float); }
    FAbsFExpr dup() { return fastalloc!(FAbsFExpr)(sup.dup); }
    void emitLLVM(LLVMFile lf) {
      todo("FAbsFExpr::emitLLVM");
      /*mixin(mustOffset("4"[]));
      sup.emitLLVM(lf);
      lf.loadFloat("(%esp)"[]);
      lf.fpuOp("fabs"[]);
      lf.storeFloat("(%esp)"[]);*/
    }
  }
}

class SSESqrtExpr : Expr {
  Expr sup;
  this(Expr ex) { sup = ex; }
  mixin defaultIterate!(sup);
  override {
    IType valueType() { return Single!(Float); }
    FSqrtExpr dup() { return fastalloc!(FSqrtExpr)(sup.dup); }
    void emitLLVM(LLVMFile lf) {
      todo("SSESqrtExpr::emitLLVM");
      /*mixin(mustOffset("4"[]));
      sup.emitLLVM(lf);
      lf.SSEOp("movd"[], "(%esp)"[], "%xmm0"[], true /* ignore stack alignment * /);
      lf.SSEOp("sqrtss"[], "%xmm0"[], "%xmm0"[]);
      lf.SSEOp("movd"[], "%xmm0"[], "(%esp)"[], true);*/
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
    if (fc.fun.name == "sqrt"[] /or/ "[wrap]sqrt"[]) {
      if (sqrmod && sqrmod.name == "std.math"[]) isSqrtMath = true;
    }
    if (fc.fun.name == "sqrtf"[] /or/ "[wrap]sqrtf"[]) {
      if (sqrmod && sysmod && sqrmod is sysmod) isSqrtfSysmod = true;
    }
    if (!isSqrtMath && !isSqrtfSysmod) return null;
    auto arg = foldex(fc.getParams()[0]);
    // return fastalloc!(FSqrtExpr)(arg);
    return fastalloc!(SSESqrtExpr)(arg);
  };
  foldopt ~= delegate Itr(Itr it) {
    auto fc = fastcast!(FunCall) (it);
    if (!fc) return null;
    bool isSinMath;
    auto sinmod = fastcast!(Module) (fc.fun.sup);
    if (fc.fun.name == "sin"[] /or/ "[wrap]sin"[]) {
      if (sinmod && sinmod.name == "std.math"[]) isSinMath = true;
    }
    if (!isSinMath) return null;
    auto arg = foldex(fc.getParams()[0]);
    return fastalloc!(FSinExpr)(arg);
  };
  foldopt ~= delegate Itr(Itr it) {
    auto fc = fastcast!(FunCall) (it);
    if (!fc) return null;
    bool isFabsMath;
    auto mod = fastcast!(Module) (fc.fun.sup);
    if (fc.fun.name != "fabsf"[] || !fc.fun.extern_c) return null;
    auto arg = foldex(fc.getParams()[0]);
    return fastalloc!(FAbsFExpr)(arg);
  };
}
