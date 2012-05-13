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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"[]));
      i.emitAsm(af);
      af.loadIntAsFloat("(%esp)"[]);
      af.storeFloat("(%esp)"[]);
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("8"[]));
      l.emitAsm(af);
      af.loadLongAsFloat("(%esp)"[]);
      af.storeDouble("(%esp)"[]);
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
        return fastalloc!(FloatExpr)(ie.num);
      }
    }
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto fc = fastcast!(FunCall) (it)) {
      if (fc.fun.extern_c && fc.fun.name == "sqrtf"[]) {
        assert(fc.params.length == 1);
        auto fe = fc.params[0];
        if (!gotImplicitCast(fe, (Expr ex) { return test(fastcast!(FloatExpr) (foldex(ex))); }))
          return null;
        return fastalloc!(FloatExpr)(sqrtf((fastcast!(FloatExpr) (foldex(fe))).f));
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("8"[]));
      (mkInt(0)).emitAsm(af);
      i.emitAsm(af);
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
    void emitAsm(AsmFile af) {
      if (lng) {
        mixin(mustOffset("8"[]));
        fp.emitAsm(af);
        if (dbl) af.loadDouble("(%esp)"[]);
        else af.loadFloat("(%esp)"[]);
        if (!dbl) af.salloc(4);
        af.storeFPAsLong("(%esp)"[]);
      } else {
        mixin(mustOffset("4"[]));
        fp.emitAsm(af);
        if (dbl) af.loadDouble("(%esp)"[]);
        else af.loadFloat("(%esp)"[]);
        if (dbl) af.sfree(4);
        af.storeFPAsInt("(%esp)"[]);
      }
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("8"[]));
      f.emitAsm(af);
      af.loadFloat("(%esp)"[]);
      af.salloc(4);
      af.storeDouble("(%esp)"[]);
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"[]));
      d.emitAsm(af);
      af.loadDouble("(%esp)"[]);
      af.sfree(4);
      af.storeFloat("(%esp)"[]);
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("2"[]));
      if (isARM) {
        af.salloc(2);
        ie.emitAsm(af);
        af.popStack("r0"[], 4);
        af.mmove2("r0"[], "[sp]"[]);
      } else {
        af.mmove2(Format("$"[], ie.num), "%ax"[]);
        af.pushStack("%ax"[], 2);
      }
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("1"[]));
      af.salloc(1);
      if (isARM) {
        af.mmove4(af.number(ie.num), "r0"[]);
        af.mmove1("r0"[], "[sp]"[]);
      } else {
        af.mmove1(af.number(ie.num), "(%esp)"[]);
      }
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("2"[]));
      ex.emitAsm(af);
      if (isARM) {
        af.popStack("r0"[], 4);
        logln("TODO: proper int to short"[]);
        af.salloc(2);
        af.mmove2("r0"[], "[sp]"[]);
        return;
      }
      af.popStack("%eax"[], 4);
      af.mmove4("%eax"[], "%ebx"[]);
      af.mathOp("shrl"[], "$16"[], "%ebx"[]); // move eah into eal
      af.mathOp("andw"[], "$32768"[], "%bx"[]); // select high bit
      af.mathOp("andw"[], "$32767"[], "%ax"[]); // mask out high bit
      af.mathOp("orw"[], "%bx"[], "%ax"[]); // copy bit
      af.pushStack("%ax"[], 2);
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("1"[]));
      ex.emitAsm(af);
      if (isARM) {
        af.mmove2("[sp]"[], "r0"[]);
        af.sfree(1);
        af.mmove1("r0"[], "[sp]"[]);
        return;
      }
      af.popStack("%ax"[], 2);
      af.pushStack("%al"[], 1);
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
    auto dex = fastcast!(DoubleExpr) (foldex(ex));
    if (!dex) return null;
    return fastalloc!(FloatExpr)(cast(float) dex.d);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    auto ie = fastcast!(IntExpr) (foldex(ex));
    if (!ie || ie.num > 65535 || ie.num < -32767) return null;
    return fastalloc!(IntLiteralAsShort)(ie);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (Single!(SysInt) != ex.valueType()) return null;
    auto ie = fastcast!(IntExpr) (foldex(ex));
    if (!ie || ie.num > 255 || ie.num < -127) return null;
    return fastalloc!(IntLiteralAsByte)(ie);
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
    if (Single!(SysInt) != resolveTup(ex.valueType()))
      return null;
    return fastalloc!(ShortAsByte)(fastalloc!(IntAsShort)(ex));
  };
}

void loadFloatEx(Expr ex, AsmFile af) {
  if (auto lv = fastcast!(CValue)~ ex) {
    lv.emitLocation(af);
    af.popStack("%eax"[], nativePtrSize);
    af.loadFloat("(%eax)"[]);
    af.nvm("%eax"[]);
  } else {
    int toFree = 4 + alignStackFor(ex.valueType(), af);
    ex.emitAsm(af);
    af.loadFloat("(%esp)"[]);
    af.sfree(toFree);
  }
}

void loadDoubleEx(Expr ex, AsmFile af) {
  if (auto cv = fastcast!(CValue)~ ex) {
    cv.emitLocation(af);
    af.popStack("%eax"[], nativePtrSize);
    af.loadDouble("(%eax)"[]);
    af.nvm("%eax"[]);
  } else {
    ex.emitAsm(af);
    af.loadDouble("(%esp)"[]);
    af.sfree(8);
  }
}

void opt(Expr ex) {
  void delegate(ref Iterable) dg;
  dg = (ref Iterable it) {
    it.iterate(dg);
    if (auto iaf = fastcast!(IntAsFloat)~ it) {
      if (auto ie = fastcast!(IntExpr)~ iaf.i) {
        it = fastalloc!(FloatExpr)(ie.num);
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
      fail;
    opt(e1);
    opt(e2);
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
    abstract void emitAsm(AsmFile af);
  }
}

class AsmIntBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) {
    super(e1, e2, op);
  }
  private this() { super(); }
  AsmIntBinopExpr dup() { return fastalloc!(AsmIntBinopExpr)(e1.dup, e2.dup, op); }
  override {
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      if (isARM) {
        e2.emitAsm(af);
        e1.emitAsm(af);
        af.popStack("r1"[], 4);
        af.popStack("r0"[], 4);
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
        af.mathOp(asmop, "r0"[], "r1"[], "r0"[]);
        af.pushStack("r0"[], 4);
        return;
      }
      if (op == "/" || op == "%"[]) {
        e2.emitAsm(af);
        e1.emitAsm(af);
        af.popStack("%eax"[], 4);
        af.extendDivide("(%esp)"[], op == "/"[]);
        af.sfree(4);
        if (op == "%"[]) {
          af.pushStack("%edx"[], 4);
          af.nvm("%edx"[]);
        } else {
          af.pushStack("%eax"[], 4);
          af.nvm("%eax"[]);
        }
      } else {
        string op1, op2;
        if (auto c2 = fastcast!(IntExpr) (e2)) {
          op2 = Format("$"[], c2.num);
        } else {
          op2 = "%ecx";
          e2.emitAsm(af);
        }
        if (auto c1 = fastcast!(IntExpr) (e1)) {
          op1 = Format("$"[], c1.num);
          af.mmove4(op1, "%edx"[]);
        } else {
          e1.emitAsm(af);
          af.popStack("%edx"[], 4);
        }
        string top = op;
        if (top == "*" && op2.startsWith("$"[])) {
          auto num = op2[1 .. $].my_atoi();
          if (num == 4) { top = "<<"; op2 = "$2"; }
        }
        
        auto asm_op = ([
          "+"[]: "addl"[], "-": "subl"[],
          "*": "imull"[], "/": "idivl"[],
          "xor": "xorl"[],
          "&": "andl"[], "|": "orl"[],
          "%": "imodl"[],
          "<<": "shl"[], ">>": "sar"[], ">>>": "shr"
        ])[top];
        
        if (op2.isRegister())
          af.popStack(op2, 4);
        
        if (asm_op == "sar" || asm_op == "shl" || asm_op == "%shr"[])
          if (op2 == "%ecx"[])
            op2 = "%cl"; // shl/r really want %cl.
        
        af.mathOp(asm_op, op2, "%edx"[]);
        af.pushStack("%edx"[], 4);
        af.nvm("%edx"[]);
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
        aibe.e1 = e1; aibe.e2 = e2; // sshhhhhhhhhh
        return null;
      }
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
    void emitAsm(AsmFile af) {
      if (op == "-"[]) (fastalloc!(AsmIntBinopExpr)(mkInt(0), ex, "-"[])).emitAsm(af);
      else if (op == "¬"[]) {
        ex.emitAsm(af);
        af.popStack("%eax"[], 4);
        af.put("notl %eax"[]);
        af.pushStack("%eax"[], 4);
      }
      else
      {
        logln("!! "[], op, " "[], ex);
        fail;
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
    AsmLongUnaryExpr dup() { return fastalloc!(AsmLongUnaryExpr)(ex.dup, op); }
    IType valueType() { return ex.valueType(); }
    void emitAsm(AsmFile af) {
      ex.emitAsm(af);
      if (op == "-"[]) {
        af.put("negl 4(%esp)"[]);
        af.put("notl (%esp)"[]);
      } else if (op == "¬"[]) {
        af.put("notl 4(%esp)"[]);
        af.put("notl (%esp)"[]);
      }
      else
      {
        logln("!! "[], op, " "[], ex);
        fail;
      }
    }
  }
}

class AsmFloatBinopExpr : BinopExpr {
  this(Expr e1, Expr e2, string op) { super(e1, e2, op); }
  private this() { super(); }
  override {
    AsmFloatBinopExpr dup() { return fastalloc!(AsmFloatBinopExpr)(e1.dup, e2.dup, op); }
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 4);
      assert(e2.valueType().size == 4);
      // TODO: belongs in optimizer
      bool commutative = op == "+" || op == "*";
      if (commutative) {
        // hackaround for circular dep avoidance
        if ((fastcast!(Object)~ e2).classinfo.name.find("Variable"[]) != -1 || fastcast!(FloatExpr)~ e2 || fastcast!(IntAsFloat)~ e2)
          swap(e1, e2); // try to eval simpler expr last
      }
      loadFloatEx(e2, af);
      loadFloatEx(e1, af);
      af.salloc(4);
      switch (op) {
        case "+": af.floatMath("fadd"[]); break;
        case "-": af.floatMath("fsub"[]); break;
        case "*": af.floatMath("fmul"[]); break;
        case "/": af.floatMath("fdiv"[]); break;
        case "%": // taken from glibc
          af.floatStackDepth --;
          af.put("1: fprem1"[]); // ieee-correct remainder
          af.put("fstsw %ax"[]); // sets parity if unfinished
          af.put("sahf"[]);
          af.put("jp 1b"[]);     // in that case, rerun it
          af.put("fstp %st(1)"[]); // pop unneeded
          break;
      }
      af.storeFloat("(%esp)"[]);
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
    void emitAsm(AsmFile af) {
      assert(e1.valueType().size == 8);
      assert(e2.valueType().size == 8);
      loadDoubleEx(e2, af);
      loadDoubleEx(e1, af);
      af.salloc(8);
      switch (op) {
        case "+": af.floatMath("fadd"[]); break;
        case "-": af.floatMath("fsub"[]); break;
        case "*": af.floatMath("fmul"[]); break;
        case "/": af.floatMath("fdiv"[]); break;
        case "%": assert(false, "Modulo not supported on floats. "[]);
      }
      af.storeDouble("(%esp)"[]);
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

static this() { parsecon.addPrecedence("tree.expr.arith"[], "12"[]); }

const oplist = [
  "+"[], "-"[], "*"[], "/"[],
  "xor"[], "|"[], "&"[], "%"[],
  "<<"[], ">>>"[], ">>"[], "^"[], "x"
];

const oplevel = [
  0, 1, 2, 2,
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
      auto op2 = lookupOp(opName, true, op, recurse(nextOp, _i + 1));
      if (!op2) { backupt2.setError("No "[], op, " defined! "[]); t2 = backupt2; return null; }
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
    if (!t2.accept("¬"[]) && !t2.accept("neg"[])) return null;
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"[]));
      sup.emitAsm(af);
      af.loadFloat("(%esp)"[]);
      af.floatMath("fsqrt"[], false);
      af.storeFloat("(%esp)"[]);
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"[]));
      sup.emitAsm(af);
      af.loadFloat("(%esp)"[]);
      af.fpuOp("fsin"[]);
      af.storeFloat("(%esp)"[]);
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"[]));
      sup.emitAsm(af);
      af.loadFloat("(%esp)"[]);
      af.fpuOp("fabs"[]);
      af.storeFloat("(%esp)"[]);
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
    void emitAsm(AsmFile af) {
      mixin(mustOffset("4"[]));
      sup.emitAsm(af);
      af.SSEOp("movd"[], "(%esp)"[], "%xmm0"[], true /* ignore stack alignment */);
      af.SSEOp("sqrtss"[], "%xmm0"[], "%xmm0"[]);
      af.SSEOp("movd"[], "%xmm0"[], "(%esp)"[], true);
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
