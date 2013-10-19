// conditionals, ie. if tests
module ast.conditionals;

import
  ast.base, ast.namespace, ast.parse, ast.math, ast.assign, ast.scopes,
  ast.casting, ast.opers,
  tools.base: This, This_fn, rmSpace;

class TrueCond : Cond {
  mixin DefaultDup!();
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    string toString() { return Format("true"[]); }
    void jumpOn(LLVMFile lf, bool cond, string dest) {
      if (cond) jump(lf, dest);
    }
  }
}

class FalseCond : Cond {
  mixin DefaultDup!();
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    string toString() { return Format("false"[]); }
    void jumpOn(LLVMFile lf, bool cond, string dest) {
      if (!cond) jump(lf, dest);
    }
  }
}

Cond exprwrap(Expr ex) {
  // unpack: ExprWrap is type agnostic anyway
  while (true) {
    if (auto rce = fastcast!(RCE) (ex)) {
      ex = rce.from;
      continue;
    }
    if (auto sl = fastcast!(StructLiteral) (ex)) {
      if (sl.exprs.length == 1) {
        ex = sl.exprs[0];
        continue;
      }
    }
    break;
  }
  if (auto ce = fastcast!(CondExpr) (ex))
    return ce.cd;
  return fastalloc!(ExprWrap)(ex);
}

import ast.structure;
class ExprWrap_ : Cond {
  Expr ex;
  this(Expr ex) {
    this.ex = ex;
    if (!ex) fail;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  Cond collapse() {
    if (auto ce = fastcast!(CondExpr)(.collapse(ex)))
      return ce.cd;
    setupStaticBoolLits();
    auto ex = .collapse(ex);
    if (isStaticTrue(ex)) return cTrue;
    if (isStaticFalse(ex)) return cFalse;
    if (auto ie = fastcast!(IntExpr)(ex))
      if (ie.num) return cTrue;
      else return cFalse;
    
    return this;
  }
  override {
    string toString() { return Format("!!"[], ex); }
    void jumpOn(LLVMFile lf, bool cond, string dest) {
      ex = reinterpret_cast(Single!(SysInt), ex);
      auto v = save(lf, ex);
      if (cond) { // jump on != 0
        v = save(lf, "icmp ne i32 0, ", v);
      } else { // jump on 0
        v = save(lf, "icmp eq i32 0, ", v);
      }
      push(lf, v);
      .jumpOn(lf, dest);
    }
  }
}

final class ExprWrap : ExprWrap_ {
  static const isFinal = true;
  this(Expr ex) { super(ex); }
}

class StatementAndCond : Cond {
  Statement first;
  Cond second;
  mixin MyThis!("first, second"[]);
  mixin DefaultDup!();
  mixin defaultIterate!(first, second);
  mixin defaultCollapse!();
  override {
    string toString() { return Format("{ "[], first, " "[], second, " }"[]); }
    void jumpOn(LLVMFile lf, bool cond, string dest) {
      mixin(mustOffset("0"));
      first.emitLLVM(lf);
      second.jumpOn(lf, cond, dest);
    }
  }
}

const bool useIVariant = true;

class Compare : Expr {
  // NEEDS "not" to handle float math correctly - !< is not the same as >=
  Expr e1; bool not, smaller, equal, greater; Expr e2;
  Expr falseOverride, trueOverride;
  bool signed;
  private this() { }
  override Compare dup() {
    auto res = new Compare(e1.dup, not, smaller, equal, greater, e2.dup, signed);
    if (falseOverride) res.falseOverride = falseOverride.dup;
    if ( trueOverride) res. trueOverride =  trueOverride.dup;
    return res;
  }
  mixin defaultIterate!(e1, e2, falseOverride, trueOverride);
  Expr collapse() {
    auto e1 = .collapse(e1);
    auto e2 = .collapse(e2);
    auto i1 = fastcast!(IntExpr) (e1);
    auto i2 = fastcast!(IntExpr) (e2);
    if (auto ce1 = fastcast!(CondExpr) (e1)) {
      Cond cd = ce1.cd;
      if (isStaticTrue (cd)) i1 = mkInt(1);
      if (isStaticFalse(cd)) i1 = mkInt(0);
    }
    if (auto ce2 = fastcast!(CondExpr) (e2)) {
      Cond cd = ce2.cd;
      if (isStaticTrue (cd)) i2 = mkInt(1);
      if (isStaticFalse(cd)) i2 = mkInt(0);
    }
    if (!i1 || !i2) return this;
    bool result;
    if (smaller && i1.num < i2.num) result = true;
    if (equal   && i1.num== i2.num) result = true;
    if (greater && i1.num > i2.num) result = true;
    if (not) result = !result;
    Expr res;
    if (result) {
      if (trueOverride) res = trueOverride;
      else if (True) res = True;
      else return this;
    } else {
      if (falseOverride) res = falseOverride;
      else if (False) res = False;
      else return this;
    }
    return res;
  }
  string toString() {
    string res;
    if (not) res ~= "!";
    if (smaller) res ~= "<";
    if (equal) res ~= "=";
    if (greater) res ~= ">";
    if (!smaller && !greater && !not) res ~= "=";
    res ~= "(";
    res ~= (fastcast!(Object)~ e1).toString();
    res ~= ", ";
    res ~= (fastcast!(Object)~ e2).toString();
    res ~= ")";
    if ( trueOverride) { res ~= "?"; res ~= (fastcast!(Object)( trueOverride)).toString(); }
    if (falseOverride) { res ~= ":"; res ~= (fastcast!(Object)(falseOverride)).toString(); }
    return res;
  }
  this(Expr e1, bool not, bool smaller, bool equal, bool greater, Expr e2, bool signed = true) {
    this.signed = signed;
    auto t1 = e1.valueType(), t2 = e2.valueType();
    if (t1.llvmSize() != "4" && t1.llvmType() != "double") {
      logln("Invalid comparison parameter: "[], e1.valueType());
      fail;
    }
    if (t2.llvmSize() != "4" && t2.llvmType() != "double") {
      logln("Invalid comparison parameter: "[], e2.valueType());
      fail;
    }
    this.e1 = e1;
    this.not = not; this.smaller = smaller; this.equal = equal; this.greater = greater;
    this.e2 = e2;
  }
  this(Expr e1, string str, Expr e2, bool signed = true) {
    auto backup = str;
    bool not, smaller, greater, equal;
    if (auto rest = str.startsWith("!"[])) { not =      true; str = rest; }
    if (auto rest = str.startsWith("<"[])) { smaller =  true; str = rest; }
    if (auto rest = str.startsWith(">"[])) { greater =  true; str = rest; }
    if (!not && !smaller && !greater) {
      if (auto rest = str.startsWith("=="[])) { equal = true; str = rest; }
    } else {
      if (auto rest = str.startsWith("="[])) { equal =  true; str = rest; }
    }
    if (str.length)
      throw new Exception("Not a valid condition string: "~backup~". "[]);
    this(e1, not, smaller, equal, greater, e2, signed);
  }
  void flip() {
    swap(e1, e2);
    swap(smaller, greater);
  }
  bool isFloat() {
    return !!(Single!(Float) == e1.valueType());
  }
  bool isDouble() {
    return !!(Single!(Double) == e1.valueType());
  }
  void prelude() {
    assert(e1.valueType().llvmType() == "i32");
    assert(e2.valueType().llvmType() == "i32");
    bool intThing1 = fastcast!(IntExpr)(e1) || fastcast!(SizeT)(e1);
    bool intThing2 = fastcast!(IntExpr)(e2) || fastcast!(SizeT)(e2);
    if (intThing1 && !intThing2)
      flip;
    if (Single!(Float) == e1.valueType() && Single!(Float) != e2.valueType()) {
      assert(Single!(SysInt) == e2.valueType());
      e2 = mkIntAsFloat(e2);
    }
    if (Single!(Float) == e2.valueType() && Single!(Float) != e1.valueType()) {
      assert(Single!(SysInt) == e1.valueType());
      e1 = mkIntAsFloat(e1);
    }
  }
  void emitWith(LLVMFile lf, bool n, bool s, bool e, bool g) {
    auto v1 = save(lf, e1), v2 = save(lf, e2);
    string ftest, itest;
    if (!n && !s && !e && !g) { itest = "false";             ftest = "false";} // unfulfillable
    if (!n && !s && !e &&  g) { itest = signed?"sgt":"ugt";  ftest = "ogt";  } // greater
    if (!n && !s &&  e && !g) { itest = "eq";                ftest = "oeq";  } // equal
    if (!n && !s &&  e &&  g) { itest = signed?"sge":"uge";  ftest = "oge";  } // greater or equal
    if (!n &&  s && !e && !g) { itest = signed?"slt":"ult";  ftest = "olt";  } // smaller
    if (!n &&  s && !e &&  g) { itest = "ne";                ftest = "one";  } // smaller or greater
    if (!n &&  s &&  e && !g) { itest = signed?"sle":"ule";  ftest = "ole";  } // smaller or equal
    if (!n &&  s &&  e &&  g) { itest = "true";              ftest = "ord";  } // smaller, greater or equal
    if ( n && !s && !e && !g) { itest = "true";              ftest = "true"; } // unfalsifiable
    if ( n && !s && !e &&  g) { itest = signed?"sle":"ule";  ftest = "ule";  } // not greater
    if ( n && !s &&  e && !g) { itest = "ne";                ftest = "une";  } // not equal
    if ( n && !s &&  e &&  g) { itest = signed?"slt":"ult";  ftest = "ult";  } // not equal or greater
    if ( n &&  s && !e && !g) { itest = signed?"sge":"uge";  ftest = "uge";  } // not smaller
    if ( n &&  s && !e &&  g) { itest = "eq";                ftest = "ueq";  } // not smaller or greater
    if ( n &&  s &&  e && !g) { itest = signed?"sgt":"ugt";  ftest = "ugt";  } // not smaller or equal
    if ( n &&  s &&  e &&  g) { itest = "false";             ftest = "uno";  } // not smaller, equal or greater
    if (isFloat()) load(lf, "fcmp ", ftest, " float ", v1, ", ", v2);
    else if (isDouble()) load(lf, "fcmp ", ftest, " double ", v1, ", ", v2);
    else {
      if (itest == "true") load(lf, "i1 1");
      else if (itest == "false") load(lf, "i1 0");
      else load(lf, "icmp ", itest, " ", typeToLLVM(e1.valueType()), " ", v1, ", ", v2);
    }
    if (falseOverride || trueOverride) {
      if (!(falseOverride && trueOverride)) {
        fail;
      }
      auto fe = save(lf, falseOverride);
      auto te = save(lf, trueOverride);
      load(lf, "select i1 ", lf.pop(), ", ",
        typeToLLVM( trueOverride.valueType()), " ", te, ", ",
        typeToLLVM(falseOverride.valueType()), " ", fe);
    }
  }
  override {
    IType valueType() {
      if (falseOverride || trueOverride) {
        assert(falseOverride && trueOverride);
        assert(falseOverride.valueType() == trueOverride.valueType());
        auto res = falseOverride.valueType();
        return res;
      }
      if (auto b = fastcast!(IType)(sysmod.lookup("bool"))) return b; // TODO cache
      return Single!(SysInt);
    }
    void emitLLVM(LLVMFile lf) {
      if (falseOverride  || trueOverride) {
        emitWith(lf, not, smaller, equal, greater);
      } else {
        emitWith(lf, not, smaller, equal, greater);
        load(lf, "zext i1 ", lf.pop(), " to i32");
      }
    }
    /*void jumpOn(LLVMFile lf, bool cond, string dest) {
      auto n = not, s = smaller, e = equal, g = greater;
      // TODO: integrate negation
      if (!cond) { // negate
        // s = !s; e = !e; g = !g; 
        n = !n;
      }
      emitWith(lf, n, s, e, g);
      .jumpOn(lf, dest);
    }*/
  }
}

Object gotIntExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr res;
  IType[] its;
  if (!rest(text, "tree.expr"[], &res))
    return null;
  if (!gotImplicitCast(res, (IType it) { its ~= it; return it.llvmType() == "i32"; }, false)) {
    text.setError("Neither of those was int sized: "[], its);
    return null;
  }
  return fastcast!(Object)~ res;
}
mixin DefaultParser!(gotIntExpr, "tree.int_expr"[]);

class NegCond : Cond {
  Cond c;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(c);
  Cond collapse() {
    auto sub = .collapse(c);
    setupStaticBoolLits();
    if (isStaticTrue(sub)) return cFalse;
    if (isStaticFalse(sub)) return cTrue;
    return this;
  }
  this(Cond c) { this.c = c; if (!c) fail; }
  override string toString() { return Format("!("[], c, ")"[]); }
  override void jumpOn(LLVMFile lf, bool cond, string dest) {
    c.jumpOn(lf, !cond, dest);
  }
}

Object gotNegate(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  auto t3 = t2;
  if (t3.accept("is") && !t3.accept("-")) return null; // "dg !is dg2" is "!(dg is dg2)", not "dg (!is (dg2))" - but also allow is-foo
  if (!rest(t2, "tree.expr _tree.expr.bin"[], &ex))
    t2.failparse("Couldn't match condition to negate"[]);
  text = t2;
  return fastcast!(Object)(cond2ex(fastalloc!(NegCond)(ex2cond(ex, true))));
}
mixin DefaultParser!(gotNegate, "tree.expr.cond_negate"[], "2103"[], "!"[]);

Cond compare(string op, Expr ex1, Expr ex2) {
  bool not, smaller, equal, greater;
  string op2 = op;
  while (op2.length) {
    if (op2[0] == '!') { not     = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '<') { smaller = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '=') { equal   = true; op2 = op2[1 .. $]; continue; }
    if (op2[0] == '>') { greater = true; op2 = op2[1 .. $]; continue; }
    fail;
  }
  {
    auto ie1 = ex1, ie2 = ex2;
    bool isInt(IType it) { return !!fastcast!(SysInt) (resolveType(it)); }
    if (gotImplicitCast(ie1, Single!(SysInt), &isInt) && gotImplicitCast(ie2, Single!(SysInt), &isInt)) {
      return exprwrap(fastalloc!(Compare)(ie1, not, smaller, equal, greater, ie2));
    }
  }
  {
    auto se1 = ex1, se2 = ex2;
    bool isSizeT(IType it) { return !!fastcast!(SizeT) (resolveType(it)); }
    if (gotImplicitCast(se1, Single!(SizeT), &isSizeT) && gotImplicitCast(se2, Single!(SizeT), &isSizeT)) {
      return exprwrap(fastalloc!(Compare)(se1, not, smaller, equal, greater, se2, false));
    }
  }
  {
    auto fe1 = ex1, fe2 = ex2;
    bool isFloat(IType it) { return !!fastcast!(Float) (resolveType(it)); }
    if (gotImplicitCast(fe1, Single!(Float), &isFloat) && gotImplicitCast(fe2, Single!(Float), &isFloat)) {
      return exprwrap(fastalloc!(Compare)(fe1, not, smaller, equal, greater, fe2));
    }
  }
  {
    auto de1 = ex1, de2 = ex2;
    bool isDouble(IType it) { return !!fastcast!(Double) (resolveType(it)); }
    if (gotImplicitCast(de1, Single!(Double), &isDouble) && gotImplicitCast(de2, Single!(Double), &isDouble)) {
      return exprwrap(fastalloc!(Compare)(de1, not, smaller, equal, greater, de2));
    }
  }
  return null; // use lookupOp directly instead
  // return ex2cond(lookupOp(op, ex1, ex2));
}

import ast.modules;
void setupStaticBoolLits() {
  if (True && False) return;
  True = fastcast!(Expr) (sysmod.lookup("true"[]));
  False = fastcast!(Expr) (sysmod.lookup("false"[]));
  opt(True); opt(False);
  cTrue = new TrueCond;
  cFalse = new FalseCond;
}

import ast.fold, ast.static_arrays;
bool isStaticTrue(Expr ex) {
  if (ex is True) return true;
  if (auto ie = fastcast!(IntExpr)(ex))
    if (ie.num) return true;
  if (auto rce = fastcast!(RCE) (ex)) {
    if (fastcast!(IType) (sysmod.lookup("bool")) == rce.to) {
      if (auto ie = fastcast!(IntExpr) (rce.from))
        if (ie.num == 1) return true;
    }
  }
  if (ex !is .collapse(ex)) {
    logln("called with uncollapsed expr");
    fail;
  }
  return false;
}

bool isStaticTrue(Cond cd) {
  if (fastcast!(TrueCond) (cd)) return true;
  auto ew = fastcast!(ExprWrap) (cd);
  if (!ew) return false;
  return isStaticTrue(.collapse(ew.ex));
}

bool isStaticFalse(Expr ex) {
  if (ex is False) return true;
  if (auto ie = fastcast!(IntExpr)(ex))
    if (!ie.num) return true;
  if (auto rce = fastcast!(RCE) (ex)) {
    if (fastcast!(IType) (sysmod.lookup("bool")) == rce.to) {
      if (auto ie = fastcast!(IntExpr) (rce.from))
        if (ie.num == 0) return true;
    }
  }
  return false;
}

bool isStaticFalse(Cond cd) {
  if (fastcast!(FalseCond) (cd)) return true;
  auto ew = fastcast!(ExprWrap) (cd);
  if (!ew) return false;
  return isStaticFalse(.collapse(ew.ex));
}

extern(C) void oop_is_comparable_sanity_check(string text, Expr ex1, Expr ex2);

static this() {
  Expr defineOpFn(bool not, bool smaller, bool greater, bool equal, bool identical, Expr ex1, Expr ex2) {
    auto finalize = delegate Expr(Cond cd) { return cond2ex(cd); };
    if (auto cmp1 = fastcast!(Compare) (ex1)) {
      ex1 = cmp1.e2;
      finalize = cmp1 /apply/ delegate Expr(Compare cmp1, Cond cd) {
        return cond2ex(fastalloc!(BooleanOp!("&&"[]))(exprwrap(cmp1), cd));
      };
    }
    auto op = (not?"!":"")~(smaller?"<":"")~(greater?">":"")~(equal?"=":"");
    if (op == "=") op = "==";
    if (identical) {
      if (not) op = "!=";
      else op = "==";
      auto vt = typeToLLVM(ex1.valueType());
      IType cmptype;
      if (vt == "i32" || vt.endsWith("*")) cmptype = Single!(SysInt);
      else if (vt == "{i8*, i8*}" || vt == "{i32, i8*}") cmptype = Single!(Long);
      else {
        todo(qformat("comparison of ", ex1.valueType(), " ", vt));
      }
      // oop_is_comparable_sanity_check(text, ex1, ex2);
      // force value comparison
      ex1 = reinterpret_cast(cmptype, ex1);
      ex2 = reinterpret_cast(cmptype, ex2);
      if (auto res = finalize(compare(op, ex1, ex2))) return res;
      return lookupOp(op, ex1, ex2);
    }
    return finalize(compare(op, ex1, ex2));
  }
  /*
  "=="[], "!="[], "is"[], "!is"[],
   "<"[], ">"[], "<="[], ">="[], "<>="[],
  "!<"[],"!>"[],"!<="[],"!>="[],"!<>="[],
  */
  //                      not   smallergreaterequalidentical
  defineOp("=="  ,stuple(false,false,false,true ,false) /apply/ &defineOpFn);
  defineOp("is"  ,stuple(false,false,false,false,true ) /apply/ &defineOpFn);
  defineOp("<"   ,stuple(false,true ,false,false,false) /apply/ &defineOpFn);
  defineOp(">"   ,stuple(false,false,true ,false,false) /apply/ &defineOpFn);
  defineOp("<="  ,stuple(false,true ,false,true ,false) /apply/ &defineOpFn);
  defineOp(">="  ,stuple(false,false,true ,true ,false) /apply/ &defineOpFn);
  defineOp("<>=" ,stuple(false,true ,true ,true ,false) /apply/ &defineOpFn);
  
  defineOp("!="  ,stuple(true ,false,false,true ,false) /apply/ &defineOpFn);
  defineOp("!is" ,stuple(true ,false,false,false,true ) /apply/ &defineOpFn);
  defineOp("!<"  ,stuple(true ,true ,false,false,false) /apply/ &defineOpFn);
  defineOp("!>"  ,stuple(true ,false,true ,false,false) /apply/ &defineOpFn);
  defineOp("!<=" ,stuple(true ,true ,false,true ,false) /apply/ &defineOpFn);
  defineOp("!>=" ,stuple(true ,false,true ,true ,false) /apply/ &defineOpFn);
  defineOp("!<>=",stuple(true ,true ,true ,true ,false) /apply/ &defineOpFn);
}

import ast.literals;
class BooleanOp(string Which) : Cond, HasInfo {
  Cond c1, c2;
  this(Cond c1, Cond c2) {
    if (!c1 || !c2) fail;
    this.c1 = c1;
    this.c2 = c2;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(c1, c2);
  Cond collapse() {
    setupStaticBoolLits();
    auto c1 = .collapse(c1), c2 = .collapse(c2);
    static if (Which == "&&") {
      if (isStaticTrue(c1)) return c2; // true&&x => x
      else if (isStaticFalse(c1)) return cFalse; // false&&x => false
      
      if (isStaticTrue(c2)) return c1; // x&&true => x
      // else if it's static false, we still have to evaluate c1
    } else static if (Which == "||") {
      if (isStaticTrue(c1)) return cTrue; // cond2 doesn't matter
      else if (isStaticFalse(c1)) return c2; // false||x => x
      
      if (isStaticFalse(c2)) return c1; // x||false => x
      // else if it's static true, we still have to evaluate c1
    }
    return this;
  }
  override {
    string getInfo()  { return Which; }
    string toString() { return Format(Which, "("[], c1, ", "[], c2, ")"[]); }
    void jumpOn(LLVMFile lf, bool cond, string dest) {
      static if (Which == "&&"[]) {
        if (cond) {
          auto past = lf.allocLabel("past_bool");
          c1.jumpOn(lf, false, past);
          c2.jumpOn(lf, true, dest);
          lf.emitLabel(past, true);
        } else {
          c1.jumpOn(lf, false, dest);
          c2.jumpOn(lf, false, dest);
        }
      } else
      static if (Which == "||"[]) {
        if (cond) {
          c1.jumpOn(lf, true, dest);
          c2.jumpOn(lf, true, dest);
        } else {
          auto past = lf.allocLabel("past_bool");
          c1.jumpOn(lf, true, past);
          c2.jumpOn(lf, false, dest);
          lf.emitLabel(past, true);
        }
      } else
      static assert(false, "unknown boolean op: "~Which);
    }
  }
}

extern(C) Cond _testTrue(Expr ex, bool nonzeroPreferred = false);
Cond ex2cond(Expr ex, bool nonzeroPreferred = false) {
  if (!ex) return null;
  if (auto ce = fastcast!(CondExpr)(ex)) {
    if (!ce.cd) fail;
    return ce.cd;
  }
  if (auto res = _testTrue(ex, nonzeroPreferred)) return res;
  logln(ex);
  breakpoint;
  throw new Exception(Format("cannot test for zero: ", ex.valueType()));
}

Expr cond2ex(Cond cd) {
  if (!cd) return null;
  if (auto ew = fastcast!(ExprWrap)(cd))
    return ew.ex;
  return fastalloc!(CondExpr)(cd);
}

alias BooleanOp!("&&"[]) AndOp;
alias BooleanOp!("||"[]) OrOp;

static this() {
  defineOp("&&", delegate Expr(Expr ex1, Expr ex2) {
    return cond2ex(fastalloc!(AndOp)(ex2cond(ex1), ex2cond(ex2)));
  });
  defineOp("||", delegate Expr(Expr ex1, Expr ex2) {
    return cond2ex(fastalloc!(OrOp)(ex2cond(ex1), ex2cond(ex2)));
  });
}

Object gotBraces(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (rest(t2, "cond"[], &cd) && t2.accept(")"[])) {
    text = t2;
    return fastcast!(Object)~ cd;
  } else return null;
}
mixin DefaultParser!(gotBraces, "cond.braces"[], "74"[], "("[]);

// pretty much only needed for iparses that use conds
Object gotNamedCond(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string id;
  if (!t2.gotIdentifier(id)) return null;
  bool retried;
  retry:
  auto thing = namespace().lookup(id);
  if (auto cd = fastcast!(Cond) (thing)) {
    text = t2;
    return fastcast!(Object)~ cd;
  } else {
    if (!retried && !thing) {
      unknownId(id, t2);
    }
    if (t2.eatDash(id)) { retried = true; goto retry; }
    return null;
  }
}
mixin DefaultParser!(gotNamedCond, "cond.named"[], "99"[]);

import ast.vardecl;
class CondExpr : Expr {
  Cond cd;
  this(Cond cd) {
    this.cd = cd;
    if (!cd) fail;
  }
  mixin defaultIterate!(cd);
  Expr collapse() {
    if (auto ew = fastcast!(ExprWrap)(.collapse(cd)))
      return ew.ex;
    return this;
  }
  override {
    string toString() { return Format("eval "[], cd); }
    IType valueType() { return fastcast!(IType) (sysmod.lookup("bool"[])); }
    CondExpr dup() { return fastalloc!(CondExpr)(cd.dup); }
    void emitLLVM(LLVMFile lf) {
      if (auto ex = fastcast!(Expr)(cd)) {
        ex.emitLLVM(lf);
      } else {
        auto res = fastalloc!(LLVMRef)(Single!(SysInt));
        res.allocate(lf);
        
        auto mns = fastalloc!(MiniNamespace)("!safecode condexpr");
        mns.sup = namespace();
        namespace.set(mns);
        auto sc = fastalloc!(Scope)();
        namespace.set(sc);
        configure(cd);
        
        auto close = sc.open(lf)();
        res.begin(lf);
        (mkAssignment(res, mkInt(0))).emitLLVM(lf);
        auto skip = lf.allocLabel("skip");
        cd.jumpOn(lf, false, skip);
        (mkAssignment(res, mkInt(1))).emitLLVM(lf);
        lf.emitLabel(skip, true);
        close(false);
        
        res.emitLLVM(lf);
        res.end(lf);
      }
    }
  }
}

Object gotCondAsExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Cond cd;
  if (!rest(t2, "cond"[], &cd)) return null;
  text = t2;
  if (auto ew = fastcast!(ExprWrap) (cd)) {
    return fastcast!(Object) (ew.ex);
  }
  return fastalloc!(CondExpr)(cd);
}
mixin DefaultParser!(gotCondAsExpr, "tree.expr.eval.cond"[], null, "eval"[]);

Expr longOp(string Code)(Expr e1, Expr e2) {
  bool isLong(Expr ex) { return test(Single!(Long) == resolveType(ex.valueType())); }
  if (!isLong(e1) && !isLong(e2))
    return null;
  if (!gotImplicitCast(e1, &isLong) || !gotImplicitCast(e2, &isLong))
    return null;
  auto pair = mkTuple(Single!(SysInt), Single!(SysInt));
  return fastalloc!(CondExpr)(
    iparse!(Cond, "long_op"[], "cond"[])
           (Code,
            "a"[], reinterpret_cast(pair, e1), "b"[], reinterpret_cast(pair, e2))
  );
}

import ast.tuples;
static this() {
  defineOp("!="[], delegate Expr(Expr ex1, Expr ex2) {
    if (auto op = lookupOp("=="[], true, ex1, ex2)) {
      return cond2ex(fastalloc!(NegCond)(ex2cond(op)));
    }
    return null;
  });
  // TODO: generalize to save 15 lines or so
  defineOp("<"[], delegate Expr(Expr ex1, Expr ex2) { return longOp!(`(a[1] < b[1]) || (a[1] == b[1] && (a[0] < b[0]))`)(ex1, ex2); });
  defineOp(">"[], delegate Expr(Expr ex1, Expr ex2) { return longOp!(`(a[1] > b[1]) || (a[1] == b[1] && (a[0] > b[0]))`)(ex1, ex2); });
  defineOp("=="[],delegate Expr(Expr ex1, Expr ex2) { return longOp!(`a[0] == b[0] && a[1] == b[1]`)(ex1, ex2); });
}
