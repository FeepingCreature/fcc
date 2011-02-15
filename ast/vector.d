module ast.vector;

import
  ast.base, ast.tuples, ast.tuple_access, ast.types, ast.fold,
  ast.fun, ast.funcall, ast.aliasing,
  ast.structure, ast.namespace, ast.modules, ast.structfuns, ast.returns;

class Vector : Type, RelNamespace, ForceAlignment {
  IType base;
  Tuple asTup;
  Tuple asFilledTup; // including filler for vec3f
  Structure asStruct;
  int len;
  override int alignment() { return 16; }
  // quietly treat n-size as n+1-size
  bool extend() { return len == 3 && (base == Single!(Float) || base == Single!(SysInt)); }
  int real_len() {
    if (extend) return len + 1;
    return len;
  }
  this(IType it, int i) {
    this.base = it;
    this.len = i;
    IType[] mew;
    for (int k = 0; k < i; ++k)
      mew ~= it;
    asTup = mkTuple(mew);
    if (extend)
      asFilledTup = mkTuple(mew ~ it);
    else
      asFilledTup = asTup;
    asStruct = mkVecStruct(this);
  }
  override {
    int size() { return asFilledTup.size; }
    string mangle() { return Format("vec_", len, "_", base.mangle()); }
    string toString() { return Format("vec(", base, ", ", len, ")"); }
    ubyte[] initval() { return asFilledTup.initval(); }
    bool isTempNamespace() { return false; }
    int opEquals(IType it) {
      if (!super.opEquals(it)) return false;
      while (true) {
        if (auto tp = fastcast!(TypeProxy)~ it)
          it = tp.actualType();
        else break;
      }
      auto vec = fastcast!(Vector)~ it;
      assert(vec);
      return vec.base == base && vec.len == len;
    }
    Object lookupRel(string str, Expr base) {
      if (!base) return null;
      if (len > 4) return null;
      bool isValidChar(char c) {
        if (len >= 1 && c == 'x') return true;
        if (len >= 2 && c == 'y') return true;
        if (len >= 3 && c == 'z') return true;
        if (len == 4 && c == 'w') return true;
        return false;
      }
      foreach (ch; str) if (!isValidChar(ch)) return null;
      if (str.length == len) {
        if (auto res = getSSESwizzle(this, base, str)) return fastcast!(Object) (res);
      }
      auto parts = getTupleEntries(reinterpret_cast(asFilledTup, base));
      Expr[] exprs;
      foreach (ch; str) {
             if (ch == 'x') exprs ~= parts[0];
        else if (ch == 'y') exprs ~= parts[1];
        else if (ch == 'z') exprs ~= parts[2];
        else if (ch == 'w') exprs ~= parts[3];
        else assert(false);
      }
      if (exprs.length == 1) return fastcast!(Object)~ exprs[0];
      auto new_vec = new Vector(this.base, exprs.length);
      if (new_vec.extend) exprs ~= new Filler(this.base);
      return fastcast!(Object)~ reinterpret_cast(new_vec, mkTupleExpr(exprs));
    }
  }
}

class Swizzle3f : Expr {
  Expr sup;
  string rule;
  this(Expr e, string r) { sup = e; rule = r; }
  private this() { }
  mixin defaultIterate!(sup);
  mixin DefaultDup!();
  override {
    IType valueType() { checkVecs(); return vec3f; }
    void emitAsm(AsmFile af) {
      int mask;
      foreach_reverse (ch; rule) switch (ch) {
        case 'x': mask = mask*4; break;
        case 'y': mask = mask*4 + 1; break;
        case 'z': mask = mask*4 + 2; break;
      }
      sup.emitAsm(af);
      af.SSEOp("movaps", "(%esp)", "%xmm0");
      af.SSEOp(qformat("shufps $", mask, ", "), "%xmm0", "%xmm0");
      af.SSEOp("movaps", "%xmm0", "(%esp)");
    }
  }
}

Expr getSSESwizzle(Vector v, Expr ex, string rule) {
  checkVecs();
  if (v != vec3f) return null;
  return new Swizzle3f(ex, rule);
}

class SSEIntToFloat : Expr {
  Expr base;
  this(Expr b) { base = b; }
  mixin defaultIterate!(base);
  SSEIntToFloat dup() { return new SSEIntToFloat(base.dup()); }
  override {
    IType valueType() { checkVecs(); return vec3f; }
    void emitAsm(AsmFile af) {
      base.emitAsm(af);
      af.SSEOp("cvtdq2ps", "(%esp)", "%xmm0");
      af.SSEOp("movaps", "%xmm0", "(%esp)");
    }
  }
}

Object gotVecConstructor(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  auto vec = fastcast!(Vector)~ resolveType(ty);
  if (!vec)
    return null;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex)) return null;
  auto ex2 = ex;
  if (gotImplicitCast(ex2, (IType it) { return test(it == vec.base); })) {
    Expr[] exs;
    for (int i = 0; i < vec.len; ++i)
      exs ~= ex2.dup;
    if (vec.extend) exs ~= new Filler(vec.base);
    text = t2;
    return fastcast!(Object)~
      reinterpret_cast(vec, new StructLiteral(vec.asStruct, exs));
  }
  checkVecs();
  retryTup:
  if (vec == vec3f && ex.valueType() == vec3i) {
    text = t2;
    return new SSEIntToFloat(ex);
  }
  auto tup = fastcast!(Tuple) (ex.valueType());
  if (!tup) t2.failparse("WTF? No tuple param for vec constructor: ", ex.valueType());
  if (tup.types.length == 1) {
    ex = getTupleEntries(ex)[0];
    goto retryTup;
  }
  if (tup) {
    if (tup.types.length != vec.len)
      throw new Exception("Insufficient elements in vec initializer! ");
    Expr[] exs;
    foreach (entry; getTupleEntries(ex)) {
      if (!gotImplicitCast(entry, (IType it) { return test(it == vec.base); }))
        throw new Exception(Format("Invalid type in vec initializer: ", entry));
      exs ~= entry;
    }
    
    if (vec.extend) exs ~= new Filler(vec.base);
    
    text = t2;
    return fastcast!(Object)~
      reinterpret_cast(vec, new StructLiteral(vec.asStruct, exs));
  }
  assert(false);
}
mixin DefaultParser!(gotVecConstructor, "tree.expr.veccon", "8");

Stuple!(Structure, Vector, Module)[] cache;
Structure mkVecStruct(Vector vec) {
  foreach (entry; cache) if (entry._2.isValid && entry._1 == vec) return entry._0;
  auto res = new Structure(null);
  res.isTempStruct = true;
  for (int i = 0; i < vec.len; ++i)
    new RelMember(["xyzw"[i]], vec.base, res);
  
  if (vec.extend)
    new RelMember(null, vec.base, res);
  
  Expr sqr(Expr ex) { return lookupOp("*", ex, ex); }
  
  {
    Expr lensq = sqr(fastcast!(Expr)~ res.lookup("x"));
    for (int i = 1; i < vec.len; ++i)
      lensq = lookupOp("+", lensq, sqr(fastcast!(Expr)~ res.lookup(["xyzw"[i]])));
    res.add(new ExprAlias(lensq, "lensq"));
  }
  
  {
    Expr sum = fastcast!(Expr)~ res.lookup("x");
    for (int i = 1; i < vec.len; ++i)
      sum = lookupOp("+", sum, fastcast!(Expr)~ res.lookup(["xyzw"[i]]));
    res.add(new ExprAlias(sum, "sum"));
  }
  
  {
    Expr lensq = fastcast!(Expr)~ res.lookup("lensq");
    Expr len;
    if (lensq.valueType() == Single!(Float) || lensq.valueType() == Single!(SysInt)) {
      len = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("sqrtf"), lensq, "sqrtf"
      );
    } else if (lensq.valueType() == Single!(Double)) {
      len = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("sqrt"), lensq, "sqrt"
      );
    }
    if (!len) logln("Can't add length for ", lensq.valueType());
    assert(!!len);
    res.add(new ExprAlias(len, "length"));
  }

  cache ~= stuple(res, vec, current_module());
  return res;
}

import ast.casting, ast.static_arrays;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = fastcast!(Vector)~ ex.valueType()) {
      return reinterpret_cast(new StaticArray(vec.base, vec.real_len()), ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = fastcast!(Vector)~ ex.valueType()) {
      return reinterpret_cast(vec.asStruct, ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = fastcast!(Vector)~ ex.valueType()) {
      return reinterpret_cast(vec.asFilledTup, ex);
    }
    return null;
  };
}

import ast.parse, ast.int_literal;
Object gotVecType(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType it;
  Expr len;
  if (!t2.accept("(")) return null;
  if (!rest(t2, "type", &it) ||
      !t2.accept(",") ||
      !rest(t2, "tree.expr", &len) ||
      !t2.accept(")"))
    t2.failparse("Fail to parse vector");
  auto ie = fastcast!(IntExpr)~ fold(len);
  if (!ie)
    text.failparse("Size parameter to vec not foldable or int");
  text = t2;
  return new Vector(it, ie.num);
}
mixin DefaultParser!(gotVecType, "type.vector", "34", "vec");

bool pretransform(ref Expr ex, ref IType it) {
  it = resolveType(it);
  if (auto tup = fastcast!(Tuple)~ it) {
    if (tup.types.length == 1) {
      ex = getTupleEntries(ex)[0];
      it = tup.types[0];
      return true;
    }
  }
  return false;
}

import ast.pointer;

Vector vec3f, vec3i;
void checkVecs() { if (!vec3f) vec3f = new Vector(Single!(Float), 3); if (!vec3i) vec3i = new Vector(Single!(SysInt), 3); }

bool gotSSEVecOp(AsmFile af, Expr op1, Expr op2, Expr res, string op) {
  mixin(mustOffset("0"));
  checkVecs;
  if (op1.valueType() != vec3f
   || op2.valueType() != vec3f)
    return false;
  if (op != "+" /or/ "-" /or/ "*" /or/ "/" /or/ "^") return false;
  void packLoad(string dest, string scrap1, string scrap2) {
    af.popStack("%eax", Single!(SysInt));
    // af.SSEOp("movaps", "(%eax)", dest);
    // recommended by the intel core opt manual, 3-50
    af.movd("(%eax)", dest);
    af.movd("8(%eax)", scrap1);
    af.SSEOp("punpckldq", scrap1, dest);
    af.movd("4(%eax)", scrap1);
    af.movd("12(%eax)", scrap2);
    af.SSEOp("punpckldq", scrap2, scrap1);
    af.SSEOp("punpckldq", scrap1, dest);
  }
  auto var1 = cast(Variable) op1, var2 = cast(Variable) op2;
  bool alignedVar1 = var1 && (var1.baseOffset & 15) == 0;
  bool alignedVar2 = var2 && (var2.baseOffset & 15) == 0;
  if (alignedVar1 && alignedVar2) {
    var1.emitLocation(af);
    var2.emitLocation(af);
    /*packLoad("%xmm1", "%xmm0", "%xmm2");
    packLoad("%xmm0", "%xmm2", "%xmm3");*/
    af.popStack("%eax", Single!(SysInt));
    af.popStack("%ebx", Single!(SysInt));
    af.SSEOp("movaps", "(%ebx)", "%xmm1");
    af.SSEOp("movaps", "(%eax)", "%xmm0");
    af.salloc(16);
  }
  if (alignedVar1 && !alignedVar2) {
    af.salloc(12);
    var1.emitLocation(af);
    op2.emitAsm(af);
    af.SSEOp("movaps", "(%esp)", "%xmm1");
    af.sfree(16);
    // logln("param 2 is ", op2, ", what to do .. ");
    packLoad("%xmm0", "%xmm2", "%xmm3");
    // af.popStack("%eax", Single!(SysInt));
    // af.SSEOp("movaps", "(%eax)", "%xmm0");
    af.salloc(4);
  }
  if (!alignedVar1 && alignedVar2) {
    af.salloc(12);
    var2.emitLocation(af);
    op1.emitAsm(af);
    af.SSEOp("movaps", "(%esp)", "%xmm0");
    af.sfree(16);
    // logln("param 1 is ", op1, ", what to do .. ");
    packLoad("%xmm1", "%xmm2", "%xmm3");
    // af.popStack("%eax", Single!(SysInt));
    // af.SSEOp("movaps", "(%eax)", "%xmm1");
    af.salloc(4);
  }
  if (!alignedVar1 && !alignedVar2) {
    op1.emitAsm(af);
    op2.emitAsm(af);
    af.SSEOp("movaps", "(%esp)", "%xmm1");
    af.sfree(16);
    af.SSEOp("movaps", "(%esp)", "%xmm0");
  }
  string sse;
  if (op == "+") sse = "addps";
  if (op == "-") sse = "subps";
  if (op == "*") sse = "mulps";
  if (op == "/") sse = "divps";
  if (op == "^") sse = "xorps";
  af.SSEOp(sse, "%xmm1", "%xmm0");
  af.SSEOp("movaps", "%xmm0", "(%esp)");
  mixin(mustOffset("-16"));
  if (auto lv = cast(LValue) res) {
    (new Assignment(lv, new Placeholder(vec3f), false, true)).emitAsm(af);
  } else if (auto mv = cast(MValue) res) {
    mv.emitAssignment(af);
  } else asm { int 3; }
  return true;
}

class Vec3fSmaller : Expr {
  Expr ex1, ex2;
  this(Expr e1, Expr e2) { this.ex1 = e1; this.ex2 = e2; }
  mixin defaultIterate!(ex1, ex2);
  mixin DefaultDup!();
  private this() { }
  override {
    IType valueType() { return Single!(SysInt); }
    void emitAsm(AsmFile af) {
      checkVecs();
      auto t1 = ex1.valueType(), t2 = ex2.valueType();
      if (vec3f != t1 || vec3f != t2) {
        logln("Fuck. ", t1, " or ", t2);
        asm { int 3; }
      }
      auto filler = alignStackFor(t1, af);
      ex1.emitAsm(af);
      ex2.emitAsm(af);
      af.SSEOp("movaps", "(%esp)", "%xmm0");
      af.sfree(16);
      af.SSEOp("movaps", "(%esp)", "%xmm1");
      af.sfree(16);
      af.sfree(filler);
      af.SSEOp("cmpltps", "%xmm0", "%xmm1");
      af.nvm("%ebx");
      af.nvm("%eax");
      af.put("movmskps %xmm1, %eax");
      af.pushStack("%eax", valueType());
    }
  }
}

import ast.vardecl, ast.assign;
class VecOp : Expr {
  IType type;
  int len;
  Expr ex1, ex2;
  string op;
  mixin defaultIterate!(ex1, ex2);
  mixin DefaultDup!();
  private this() { }
  this(IType it, int len, Expr ex1, Expr ex2, string op) {
    this.type = it; this.len = len;
    this.ex1 = ex1; this.ex2 = ex2;
    this.op = op;
  }
  override {
    IType valueType() { return new Vector(type, len); }
    void emitAsm(AsmFile af) {
      auto t1 = ex1.valueType(), t2 = ex2.valueType();
      while (pretransform(ex1, t1) || pretransform(ex2, t2)) { }
      auto e1v = fastcast!(Vector)~ t1, e2v = fastcast!(Vector)~ t2;
      mkVar(af, valueType(), true, (Variable var) {
        auto entries = getTupleEntries(
          reinterpret_cast(
            fastcast!(IType)~ (fastcast!(Vector)~ valueType()).asFilledTup,
            fastcast!(LValue)~ var
        ));
        void delegate() dg1, dg2;
        mixin(mustOffset("0"));
        auto filler1 = alignStackFor(t1, af); auto v1 = mkTemp(af, ex1, dg1);
        auto filler2 = alignStackFor(t2, af); auto v2 = mkTemp(af, ex2, dg2);
        if (!gotSSEVecOp(af, fastcast!(Expr) (v1), fastcast!(Expr) (v2), fastcast!(Expr) (var), op)) {
          for (int i = 0; i < len; ++i) {
            Expr l1 = v1, l2 = v2;
            if (e1v) l1 = getTupleEntries(reinterpret_cast(fastcast!(IType)~ e1v.asFilledTup, fastcast!(LValue)~ v1))[i];
            if (e2v) l2 = getTupleEntries(reinterpret_cast(fastcast!(IType)~ e2v.asFilledTup, fastcast!(LValue)~ v2))[i];
            (new Assignment(fastcast!(LValue)~ entries[i], lookupOp(op, l1, l2))).emitAsm(af);
          }
        }
        if (dg2) dg2(); af.sfree(filler2);
        if (dg1) dg1(); af.sfree(filler1);
      });
    }
  }
}

class FailExpr : Expr {
  string mesg;
  IType typeMaybe;
  this(string s, IType tm = null) { this.mesg = s; typeMaybe = tm; }
  void fail() { logln("Fail: ", mesg); asm { int 3; } }
  override {
    IType valueType() { if (typeMaybe) return typeMaybe; fail(); return null; }
    void emitAsm(AsmFile af) { fail(); }
    mixin defaultIterate!();
    FailExpr dup() { return this; }
  }
}

import ast.opers;
static this() {
  Expr handleVecOp(string op, Expr lhs, Expr rhs) {
    auto v1 = lhs.valueType(), v2 = rhs.valueType();
    while (pretransform(lhs, v1) || pretransform(rhs, v2)) { }
    
    auto v1v = fastcast!(Vector)~ v1, v2v = fastcast!(Vector)~ v2;
    if (!v1v && !v2v) return null;
    
    assert(!v1v || !v2v || v1v.asTup.types.length == v2v.asTup.types.length, Format("Mismatching tuple types: ", v1v, " and ", v2v));
    int len;
    if (v1v) len = v1v.asTup.types.length;
    else len = v2v.asTup.types.length;
    
    IType type;
    if (v1v is v2v && v1v == v2v) type = v1v.base;
    else {
      auto l1 = lhs; if (v1v) l1 = getTupleEntries(reinterpret_cast(v1v.asFilledTup, lhs))[0];
      auto r1 = rhs; if (v2v) r1 = getTupleEntries(reinterpret_cast(v2v.asFilledTup, rhs))[0];
      type = lookupOp(op, l1, r1).valueType();
    }
    return new VecOp(type, len, lhs, rhs, op);
  }
  Expr negate(Expr ex) {
    auto ty = resolveType(ex.valueType());
    logln("negate? ", ty);
    auto vt = fastcast!(Vector)~ ty;
    if (!vt) return null;
    
    Expr[] list;
    foreach (ex2; getTupleEntries(reinterpret_cast(vt.asFilledTup, ex))[0 .. $-vt.extend]) {
      list ~= lookupOp("-", ex2);
    }
    if (vt.extend) list ~= new Filler(vt.base);
    return reinterpret_cast(vt, new StructLiteral(vt.asFilledTup.wrapped, list));
  }
  Expr handleVecSmaller(Expr e1, Expr e2) {
    auto t1 = resolveType(e1.valueType()), t2 = resolveType(e2.valueType());
    auto v1 = fastcast!(Vector) (t1), v2 = fastcast!(Vector) (t2);
    if (!v1 || !v2) return null;
    
    return lookupOp("&", new Vec3fSmaller(e1, e2), mkInt(7));
  }
  defineOp("-", &negate);
  defineOp("-", "-" /apply/ &handleVecOp);
  defineOp("+", "+" /apply/ &handleVecOp);
  defineOp("*", "*" /apply/ &handleVecOp);
  defineOp("/", "/" /apply/ &handleVecOp);
  defineOp("^", "^" /apply/ &handleVecOp);
  defineOp("<", &handleVecSmaller);
  foldopt ~= delegate Expr(Expr ex) {
    if (auto mae = fastcast!(MemberAccess_Expr) (ex)) {
      auto base = foldex(mae.base);
      if (auto rce = fastcast!(RCE) (base)) {
        if (auto vo = cast(VecOp) rce.from) {
          assert(mae.stm.offset % vo.type.size() == 0);
          auto id = mae.stm.offset / vo.type.size();
          auto ex1 = vo.ex1, ex2 = vo.ex2;
          auto t1 = ex1.valueType(), t2 = ex2.valueType();
          while (pretransform(ex1, t1) || pretransform(ex2, t2)) { }
          auto t1v = fastcast!(Vector) (t1), t2v = fastcast!(Vector) (t2);
          // logln("id is ", id, " because of ", mae.stm.offset, " into ", vo.type.size(), "; compare ", vo.valueType().size(), " / ", (cast(Vector) vo.valueType()).real_len());
          if (t1v) ex1 = getTupleEntries(reinterpret_cast(t1v.asFilledTup, ex1))[id];
          if (t2v) {
            // logln("filled tup for ", t2v, " is ", t2v.asFilledTup, " -- ", ex);
            auto ar = getTupleEntries(reinterpret_cast(t2v.asFilledTup, ex2));
            if (ar.length !> id) ex2 = new FailExpr("oh fuck", ar[0].valueType());
            else ex2 = ar[id];
          }
          return lookupOp(vo.op, ex1, ex2);
        }
      }
    }
    return null;
  };
}

class XMM : MValue {
  int which;
  this(int w) { which = w; }
  mixin defaultIterate!();
  override {
    XMM dup() { return this; }
    IType valueType() { checkVecs(); return vec3f; /* TODO: vec4f? */ }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("16"));
      af.salloc(16);
      af.SSEOp("movaps", qformat("%xmm", which), "(%esp)");
    }
    void emitAssignment(AsmFile af) {
      mixin(mustOffset("-16"));
      af.SSEOp("movaps", "(%esp)", qformat("%xmm", which));
      af.sfree(16);
    }
  }
}

Object gotXMM(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("[")) t2.failparse("Expected [index] for SSE op");
  Expr ex;
  if (!rest(t2, "tree.expr", &ex) || !t2.accept("]"))
    t2.failparse("Expected index expression for SSE op! ");
  auto lit = cast(IntExpr) foldex(ex);
  if (!lit)
    t2.failparse("Expected integer constant for SSE reg access! ");
  text = t2;
  return new XMM(lit.num);
}
mixin DefaultParser!(gotXMM, "tree.expr.xmm", "2406", "xmm");
