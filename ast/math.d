module ast.math;

import ast.base, ast.namespace, ast.parse;
import tools.base: This, This_fn, rmSpace, and, or, find, todg, fix;

Object function(ref string, Object, PropArgs, ParseCb, ParseCb, bool rawmode = false) getPropertiesFn;
void function(void delegate(PropArgs)) withPropcfgFn;

class IntAsFloat : Expr {
  Expr i;
  this(Expr i) { this.i = i; assert(Single!(SysInt) == i.valueType()); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(i);
  override {
    string toString() { return qformat("float:", i); }
    IType valueType() { return Single!(Float); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "sitofp i32 ", save(lf, i), " to float");
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
    string toString() { return qformat("double:", l); }
    IType valueType() { return Single!(Double); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "sitofp i64 ", save(lf, l), " to double");
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
    string toString() { return qformat("int:", l); }
    IType valueType() { return Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "trunc i64 ", save(lf, l), " to i32");
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
    string toString() { return qformat("long:", i); }
    IType valueType() { return Single!(Long); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "sext i32 ", save(lf, i), " to i64");
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
      string from, to;
      if (dbl) from = "double"; else from = "float";
      if (lng) to   = "i64"   ; else to   = "i32"  ;
      load(lf, "fptosi ", from, " ", save(lf, fp), " to ", to);
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
    string toString() { return qformat("double:", f); }
    IType valueType() { return Single!(Double); }
    void emitLLVM(LLVMFile lf) {
      load(lf, "fpext float ", save(lf, f), " to double");
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
      load(lf, "fptrunc double ", save(lf, d), " to float");
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
      push(lf, ie.num);
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
      push(lf, ie.num);
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
      load(lf, "trunc i32 ", save(lf, ex), " to i16");
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
      load(lf, "trunc i16 ", save(lf, ex), " to i8");
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
    debug if (qformat(this).length > 16384) {
      logln("uh oh ", this);
      fail;
    }
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
      auto v1 = save(lf, e1), v2 = save(lf, e2);
      string cmd;
      switch (op) {
        case "+": cmd = "add"; break;
        case "-": cmd = "sub"; break;
        case "*": cmd = "mul"; break;
        case "/": cmd = "sdiv"; break;
        case "xor":cmd= "xor"; break;
        case "&": cmd = "and"; break;
        case "|": cmd = "or" ; break;
        case "%": cmd = "urem";break;
        case "<<":cmd = "shl"; break;
        case ">>":cmd = "ashr";break;
        case ">>>":cmd= "lshr";break;
      }
      load(lf, cmd, " i32 ", v1, ", ", v2);
      assert(e1.valueType().llvmType() == "i32");
      assert(e2.valueType().llvmType() == "i32");
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
      if (op == "-"[]) (fastalloc!(AsmIntBinopExpr)(mkInt(0), ex, "-")).emitLLVM(lf);
      else if (op == "¬"[]) (fastalloc!(AsmIntBinopExpr)(mkInt(-1), ex, "xor")).emitLLVM(lf);
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
      assert(e1.valueType().llvmType() == "float");
      assert(e2.valueType().llvmType() == "float");
      auto v1 = save(lf, e1), v2 = save(lf, e2);
      string cmd;
      switch (op) {
        case "+": cmd = "add"; break;
        case "-": cmd = "sub"; break;
        case "*": cmd = "mul"; break;
        case "/": cmd = "div"; break;
        case "%": // TODO check for x87
          // the reason for this is that frem gets compiled to fmodf which is slow on x86.
          // shame, llvm.
          load(lf, "tail call float asm \"1: fprem\nfnstsw %ax\nsahf\njp 1b\", \"={st},{st},{st(1)},~{ax},~{fpsr},~{flags},~{dirflag}\"(float ", v1, ", float ", v2, ")");
          return;
          // cmd = "rem"; break;
      }
      // load(lf, "f", cmd, " float ", v1, ", ", v2, ", !fpmath !0");
      load(lf, "f", cmd, " fast float ", v1, ", ", v2);
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
        case "%": return fastalloc!(FloatExpr)(fe1.f % fe2.f);
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
      assert(e1.valueType().llvmType() == "double");
      assert(e2.valueType().llvmType() == "double");
      auto v1 = save(lf, e1), v2 = save(lf, e2);
      string cmd;
      switch (op) {
        case "+": cmd = "add"; break;
        case "-": cmd = "sub"; break;
        case "*": cmd = "mul"; break;
        case "/": cmd = "div"; break;
        case "%": cmd = "rem"; break;
      }
      load(lf, "f", cmd, " double ", v1, ", ", v2);
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
    
    withPropcfgFn((PropArgs args) {
      if (auto res = getPropertiesFn(
          t2, fastcast!(Object) (curOp), args, cont, rest
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

class IntrinsicExpr : Expr {
  string name;
  Expr[] args;
  IType vt;
  this(string name, Expr[] exs, IType vt) { this.name = name; args = exs; this.vt = vt; }
  mixin defaultIterate!(args);
  override {
    IType valueType() { return vt; }
    IntrinsicExpr dup() { return fastalloc!(IntrinsicExpr)(name, args.dup, vt); }
    string toString() { return qformat(name, "(", args, ")"); }
    void emitLLVM(LLVMFile lf) {
      if (once(lf, "intrinsic ", name)) {
        string argstr;
        foreach (arg; args) {
          if (argstr.length) argstr ~= ", ";
          argstr ~= typeToLLVM(arg.valueType());
        }
        lf.decls[name] = qformat("declare float @", name, " (", argstr, ")");
      }
      string argstr;
      foreach (arg; args) {
        if (argstr.length) argstr ~= ", ";
        argstr ~= qformat(typeToLLVM(arg.valueType()), " ", save(lf, arg));
      }
      load(lf, "call ", typeToLLVM(vt), " @", name, " (", argstr, ")");
    }
  }
}
