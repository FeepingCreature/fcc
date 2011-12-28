module ast.vector;

import
  ast.base, ast.tuples, ast.tuple_access, ast.types, ast.fold,
  ast.fun, ast.funcall, ast.aliasing, ast.conditionals,
  ast.structure, ast.namespace, ast.modules, ast.structfuns, ast.returns;

class ZeroFiller : Expr {
  IType type;
  this(IType type) { this.type = type; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("type.size"));
      if (fastcast!(SysInt) (type)) { af.pushStack("$0", 4); }
      else if (fastcast!(Float) (type)) {
        (new FloatExpr(0)).emitAsm(af);
      } else {
        throw new Exception(Format("Don't know how to zero ", type, "!"));
      }
    }
  }
}

Expr[] genInitPattern(int i, int len) {
  Expr[] res;
  for (int k = 0; k < len; ++k) {
    res ~= mkInt(i == k); // tee hee
  }
  return res;
}

class Vector : Type, RelNamespace, ForceAlignment, ExprLikeThingy {
  IType base;
  Tuple asTup;
  Tuple asFilledTup; // including filler for vec3f
  Structure asStruct;
  int len;
  override int alignment() {
    if (base.size < 4 || len < 3) return 4;
    return 16;
  }
  override bool isPointerLess() { return base.isPointerLess(); }
  // quietly treat n-size as n+1-size
  bool extend() { return len == 3 && (base == Single!(Float) || base == Single!(SysInt) || base == Single!(Double)); }
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
      auto vec = fastcast!(Vector) (resolveType(it));
      if (!vec) return false;
      return vec.base == base && vec.len == len;
    }
    Object lookupRel(string str, Expr base) {
      if (!base) {
        if (len > 0 && str == "X") return fastcast!(Object) (constructVector(mkTupleValueExpr(genInitPattern(0, len)), this));
        if (len > 1 && str == "Y") return fastcast!(Object) (constructVector(mkTupleValueExpr(genInitPattern(1, len)), this));
        if (len > 2 && str == "Z") return fastcast!(Object) (constructVector(mkTupleValueExpr(genInitPattern(2, len)), this));
        if (len > 3 && str == "W") return fastcast!(Object) (constructVector(mkTupleValueExpr(genInitPattern(3, len)), this));
        return null;
      }
      if (len > 4) return null;
      bool isValidChar(char c) {
        if (len >= 1 && c == 'x') return true;
        if (len >= 2 && c == 'y') return true;
        if (len >= 3 && c == 'z') return true;
        if (len == 4 && c == 'w') return true;
        return false;
      }
      foreach (ch; str) if (!isValidChar(ch)) return null;
      if (auto res = getSSESwizzle(this, base, str)) return fastcast!(Object) (res);
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
      auto new_vec = mkVec(this.base, exprs.length);
      if (new_vec.extend) exprs ~= new ZeroFiller(this.base);
      return fastcast!(Object)~ reinterpret_cast(new_vec, mkTupleExpr(exprs));
    }
  }
}

class SSESwizzle : Expr {
  Expr sup;
  string rule;
  IType type;
  this(Expr e, IType t, string r) { sup = e; type = t; rule = r; if (sup.valueType().size != type.size) { logln("sup ", sup, ", type ", type, ". "); fail; } }
  private this() { }
  mixin defaultIterate!(sup);
  mixin DefaultDup!();
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) {
      int mask;
      foreach_reverse (ch; rule) switch (ch) {
        case 'x': mask = mask*4 + 0; break;
        case 'y': mask = mask*4 + 1; break;
        case 'z': mask = mask*4 + 2; break;
        case 'w': mask = mask*4 + 3; break;
      }
      if (auto cv = fastcast!(CValue) (sup)) {
        cv.emitLocation(af);
        af.popStack("%eax", 4);
        af.SSEOp("movups", "(%eax)", "%xmm0");
        af.nvm("%eax");
        af.salloc(16);
      } else {
        sup.emitAsm(af);
        af.SSEOp("movaps", "(%esp)", "%xmm0");
      }
      af.SSEOp(qformat("shufps $", mask, ", "), "%xmm0", "%xmm0");
      af.SSEOp("movaps", "%xmm0", "(%esp)");
    }
  }
}

Expr getSSESwizzle(Vector v, Expr ex, string rule) {
  checkVecs();
  if (v != vec3f && v != vec4f) return null;
  Vector v2;
  if (rule.length == 3) v2 = vec3f;
  if (rule.length == 4) v2 = vec4f;
  if (!v2) return null;
  return new SSESwizzle(ex, v2, rule);
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

class MultiplesExpr : Expr {
  Expr base;
  int factor;
  IType type;
  this(Expr b, int f) {
    this.base = b;
    this.factor = f;
    IType[] types;
    types ~= b.valueType();
    for (int i = 1; i < factor; ++i)
      types ~= types[0];
    this.type = mkTuple(types);
  }
  mixin defaultIterate!(base);
  override {
    MultiplesExpr dup() { return new MultiplesExpr(base.dup, factor); }
    IType valueType() { return type; }
    void emitAsm(AsmFile af) {
      base.emitAsm(af);
      auto bvts = base.valueType().size;
      for (int i = 1; i < factor; ++i) {
        af.pushStack("(%esp)", bvts);
      }
    }
  }
}

import ast.literals;
class AlignedVec4Literal : Expr, Literal {
  string id;
  IType type;
  FloatExpr base; int len;
  this(IType t, FloatExpr fe, int l) { type = t; base = fe; len = l; }
  string getID(AsmFile af) {
    if (!id) {
      float[4] meep;
      foreach (ref v; meep) v = base.f;
      id = af.allocConstant(Format("__vec_constant_", af.constants.length), cast(ubyte[]) meep.dup);
    }
    return id;
  }
  override {
    mixin defaultIterate!(base);
    typeof(this) dup() { return new typeof(this) (type, base, len); }
    IType valueType() { return type; }
    string getValue() { assert(false, "Use getID instead! "); }
    void emitAsm(AsmFile af) {
      // af.put("#avlit of ", type, " * ", len);
      for (int i = 0; i < len; ++i)
        base.emitAsm(af);
    }
  }
}

static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto me = fastcast!(MultiplesExpr) (it);
    if (!me) return null;
    bool canDup; // no side effects
    auto fbase = foldex(me.base);
    if (auto lt = fastcast!(Literal) (fbase)) {
      if (me.factor == 3 || me.factor == 4) if (auto fe = fastcast!(FloatExpr) (lt)) {
        return new AlignedVec4Literal(me.type, fe, me.factor);
      }
      canDup = true;
    }
    if (auto var = fastcast!(Variable) (fbase)) canDup = true;
    if (!canDup) {
      // logln("me of ", foldex(me.base));
      return null;
    }
    Expr[] list;
    for (int i = 0; i < me.factor; ++i) list ~= fbase;
    return fastcast!(Itr) (reinterpret_cast(me.type, mkTupleExpr(list)));
  };
  foldopt ~= delegate Itr(Itr it) {
    auto mae = fastcast!(MemberAccess_Expr) (it);
    if (!mae) return null;
    auto rce = fastcast!(RCE) (foldex(mae.base));
    if (!rce) return null;
    auto fe = foldex(rce.from);
    auto mult = fastcast!(MultiplesExpr) (fe);
    auto avlit = fastcast!(AlignedVec4Literal) (fe);
    if (!mult && !avlit) return null;
    IType basetype; Expr res;
    if (mult) { basetype = mult.base.valueType(); res = mult.base; }
    if (avlit) { basetype = avlit.base.valueType(); res = avlit.base; }
    if (basetype != mae.stm.type) {
      logln("type mismatch: accessing ", mae.stm.type, " from set of ",
        basetype);
      fail;
      return null;
    }
    return fastcast!(Iterable) (res);
  };
}

Object constructVector(Expr base, Vector vec) {
  auto ex2 = base;
  if (gotImplicitCast(ex2, (IType it) { return test(it == vec.base); })) {
    return fastcast!(Object) (reinterpret_cast(
      vec,
      new MultiplesExpr(ex2, vec.real_len())
    ));
  }
  checkVecs();
  retryTup:
  if (vec == vec3f && base.valueType() == vec3i) {
    return new SSEIntToFloat(base);
  }
  auto tup = fastcast!(Tuple) (base.valueType());
  if (!tup) throw new Exception(Format("WTF? No tuple param for vec constructor: ", base.valueType()));
  if (tup.types.length == 1) {
    base = getTupleEntries(base)[0];
    goto retryTup;
  }
  if (tup) {
    if (tup.types.length != vec.len)
      throw new Exception(Format("Insufficient elements in vec initializer! "));
    Expr[] exs;
    foreach (entry; getTupleEntries(base)) {
      if (!gotImplicitCast(entry, (IType it) { return test(it == vec.base); }))
        throw new Exception(Format("Invalid type in vec initializer: ", entry));
      exs ~= entry;
    }
    
    if (vec.extend) exs ~= new ZeroFiller(vec.base);
    
    return fastcast!(Object)~
      reinterpret_cast(vec, new StructLiteral(vec.asStruct, exs));
  }
  assert(false);
}

Object gotVecConstructor(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (t2.accept("\"") || t2.accept("[")) return null;
  if (!rest(t2, "type", &ty)) {
    // logln("fail 1 @", t2.mystripl().nextText());
    return null;
  }
  auto vec = fastcast!(Vector) (resolveType(ty));
  if (!vec) {
    // logln("fail 2 @", t2.nextText());
    return null;
  }
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex)) return null;
  try {
    if (auto res = constructVector(ex, vec)) {
      text = t2;
      return res;
    }
  } catch (Exception ex) t2.failparse(ex);
  return null;
}
mixin DefaultParser!(gotVecConstructor, "tree.expr.veccon", "2407");

class FastVec3Sum : Expr {
  Expr base;
  this(Expr b) { base = b; }
  override {
    mixin defaultIterate!(base);
    FastVec3Sum dup() { return new FastVec3Sum(base.dup); }
    IType valueType() { return Single!(Float); }
    void emitAsm(AsmFile af) {
      auto filler = alignStackFor(base.valueType(), af);
      base.emitAsm(af);
      af.SSEOp("movaps", "(%esp)", "%xmm0");
      if ("sse3" in af.processorExtensions) {
        af.SSEOp("movaps", "%xmm0", "%xmm1");
        af.SSEOp("haddps", "%xmm1", "%xmm1"); // [x+y, z+w, x+y, z+w]
        af.SSEOp(qformat("shufps $", 0b1010_1010, ", "), "%xmm0", "%xmm0"); // zzzz
        af.SSEOp("addss", "%xmm1", "%xmm0");
      } else {
        af.SSEOp("movaps", "%xmm0", "%xmm1");
        af.SSEOp("movaps", "%xmm0", "%xmm2");
        af.SSEOp(qformat("shufps $", 0b0101_0101, ", "), "%xmm1", "%xmm1"); // yyyy
        af.SSEOp(qformat("shufps $", 0b1010_1010, ", "), "%xmm2", "%xmm2"); // zzzz
        af.SSEOp("addss", "%xmm1", "%xmm0");
        af.SSEOp("addss", "%xmm2", "%xmm0");
      }
      af.sfree(12 + filler);
      af.SSEOp("movd", "%xmm0", "(%esp)", true /* ignore stack alignment */);
    }
  }
}

class FastVec3Norm : Expr {
  Expr base; IType vec;
  this(Expr b, IType v) { base = b; vec = v; }
  override {
    mixin defaultIterate!(base);
    FastVec3Norm dup() { return new FastVec3Norm(base.dup, vec); }
    IType valueType() { return vec; }
    void emitAsm(AsmFile af) {
      base.emitAsm(af);
      af.SSEOp("movaps", "(%esp)", "%xmm0");
      af.SSEOp("movaps", "%xmm0", "%xmm3");
      af.SSEOp("mulps", "%xmm3", "%xmm3");
      af.SSEOp("movaps", "%xmm3", "%xmm1");
      af.SSEOp("movaps", "%xmm3", "%xmm2");
      af.SSEOp(qformat("shufps $", 0b0101_0101, ", "), "%xmm1", "%xmm1"); // yyyy
      af.SSEOp(qformat("shufps $", 0b1010_1010, ", "), "%xmm2", "%xmm2"); // zzzz
      af.SSEOp("addss", "%xmm1", "%xmm3");
      af.SSEOp("addss", "%xmm2", "%xmm3");
      af.SSEOp("rsqrtss", "%xmm3", "%xmm3");
      af.SSEOp(qformat("shufps $", 0b0000_0000, ", "), "%xmm3", "%xmm3"); // spread
      af.SSEOp("mulps", "%xmm3", "%xmm0");
      af.SSEOp("movaps", "%xmm0", "(%esp)");
    }
  }
}

import ast.templ, ast.math;
Stuple!(Structure, Vector, Module)[] cache;
Structure mkVecStruct(Vector vec) {
  foreach (entry; cache) if (entry._2.isValid && entry._1 == vec) return entry._0;
  auto res = new Structure(null);
  res.isTempStruct = true;
  res.sup = sysmod;
  auto backup = namespace();
  namespace.set(res);
  scope(exit) namespace.set(backup);
  for (int i = 0; i < vec.len; ++i)
    new RelMember(["xyzw"[i]], vec.base, res);
  
  if (vec.extend)
    new RelMember(null, vec.base, res);
  
  res.add(new RelMember("self", vec, 0));
  
  Expr sqr(Expr ex) { return lookupOp("*", ex, ex); }
  
  {
    Expr lensq = sqr(fastcast!(Expr)~ res.lookup("x"));
    for (int i = 1; i < vec.len; ++i)
      lensq = lookupOp("+", lensq, sqr(fastcast!(Expr)~ res.lookup(["xyzw"[i]])));
    res.add(new ExprAlias(lensq, "lensq"));
    res.add(new ExprAlias(lensq, "selfdot"));
  }
  
  {
    Expr sum;
    if (vec.len == 3 && vec.base == Single!(Float)) {
      sum = new FastVec3Sum(fastcast!(Expr) (res.lookup("self")));
    } else {
      sum = fastcast!(Expr)~ res.lookup("x");
      for (int i = 1; i < vec.len; ++i)
        sum = lookupOp("+", sum, fastcast!(Expr)~ res.lookup(["xyzw"[i]]));
    }
    res.add(new ExprAlias(sum, "sum"));
  }
  
  res.add(new TypeAlias(vec.base, "base"));
  // auto vv = new RelMember("vec", vec, 0);
  // res.add(new ExprAlias(reinterpret_cast(vec, fastcast!(Expr) (vv)), "vec"));
  
  if (vec.len == 3) {
    {
      auto tmpl = new Template;
      tmpl.name = "ex";
      tmpl.isAlias = true;
      tmpl.param = "A";
      tmpl.source = `alias ex = vec(base, 3)(mixin replace(A, "%", "x"), mixin replace(A, "%", "y"), mixin replace(A, "%", "z")); `;
      res.add(tmpl);
    }
  }
  
  {
    Expr lensq = fastcast!(Expr)~ res.lookup("lensq");
    Expr sum = fastcast!(Expr) (res.lookup("sum"));
    Expr len;
    Expr weirdlen;
    if (lensq.valueType() == Single!(Float) || lensq.valueType() == Single!(SysInt)) {
      len = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("sqrtf"), lensq, "sqrtf"
      );
      weirdlen = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("sqrtf"), sum, "sqrtf"
      );
    } else if (lensq.valueType() == Single!(Double) || lensq.valueType() == Single!(Long)) {
      auto mylensq = lensq, mysum = sum;
      if (mylensq.valueType() == Single!(Long)) {
        mylensq = new LongAsDouble(mylensq);
        mysum = new LongAsDouble(mysum);
      }
      len = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("sqrt"), mylensq, "sqrt"
      );
      weirdlen = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("sqrt"), mysum, "sqrt"
      );
    }
    res.add(new ExprAlias(new FastVec3Norm(fastcast!(Expr) (res.lookup("self")), vec), "normalized"));
    if (!len) logln("Can't add length for ", lensq.valueType());
    assert(!!len);
    assert(!!weirdlen);
    res.add(new ExprAlias(len, "magnitude"));
    res.add(new ExprAlias(weirdlen, "sqrt_sum"));
  }

  cache ~= stuple(res, vec, current_module());
  return res;
}

import ast.casting, ast.static_arrays;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = fastcast!(Vector)~ ex.valueType()) {
      return reinterpret_cast(vec.asStruct, ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = fastcast!(Vector)~ ex.valueType()) {
      return reinterpret_cast(new StaticArray(vec.base, vec.real_len()), ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (vec3f && ex.valueType() == vec3f)
      return reinterpret_cast(vec4f, ex);
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (auto vec = fastcast!(Vector)~ ex.valueType()) {
      if (vec.asFilledTup != vec.asTup) {
        auto filled = reinterpret_cast(vec.asFilledTup, ex);
        auto entries = getTupleEntries(filled);
        assert(entries.length == 4);
        return mkTupleExpr(entries[0], entries[1], entries[2]);
      } else
        return reinterpret_cast(vec.asTup, ex);
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
  return mkVec(it, ie.num);
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

Vector[Stuple!(IType, int)] vec_cache;
Vector mkVec(IType base, int len) {
  auto tup = stuple(base, len);
  if (auto p = tup in vec_cache) return *p;
  auto res = new Vector(base, len);
  vec_cache[tup] = res;
  return res;
}

Vector vec3f, vec4f, vec3i;
void checkVecs() {
  if (!vec3f) vec3f = mkVec(Single!(Float), 3);
  if (!vec4f) vec4f = mkVec(Single!(Float), 4);
  if (!vec3i) vec3i = mkVec(Single!(SysInt), 3);
}

string getAddr(AsmFile af, Expr src) {
  if (auto rce = fastcast!(RCE) (src)) src = rce.from; // immaterial
  if (auto xmm = fastcast!(XMM) (src)) return xmm.getValue();
  else if (auto lit = fastcast!(AlignedVec4Literal) (src)) return lit.getID(af);
  else return null;
}

bool emitUnalignedAddr(AsmFile af, Expr src) {
  if (auto cv = fastcast!(CValue) (src)) {
    cv.emitLocation(af);
    return true;
  } else return false;
}

bool gotSSEVecOp(AsmFile af, Expr op1, Expr op2, Expr res, string op) {
  mixin(mustOffset("0"));
  checkVecs;
  if (op1.valueType() != vec3f && op1.valueType() != vec4f
   || op2.valueType() != vec3f && op2.valueType() != vec4f
   || op1.valueType() != op2.valueType())
    return false;
  if (op != "+"[] /or/ "-"[] /or/ "*"[] /or/ "/"[] /or/ "^"[]) return false;
  void packLoad(string dest, string scrap1, string scrap2) {
    af.popStack("%eax", 4);
    // af.SSEOp("movaps", "(%eax)", dest);
    // recommended by the intel core opt manual, 3-50
    // also benchmarked and YES it's faster .. IFF there's a dependency.
    af.movd("(%eax)", dest);
    af.movd("8(%eax)", scrap1);
    af.SSEOp("punpckldq", scrap1, dest); // can't do directly! punpckldq requires alignment; movd doesn't.
    af.movd("4(%eax)", scrap1);
    af.movd("12(%eax)", scrap2);
    af.SSEOp("punpckldq", scrap2, scrap1);
    af.SSEOp("punpckldq", scrap1, dest);
  }
  auto var1 = fastcast!(Variable) (op1), var2 = fastcast!(Variable) (op2);
  bool alignedVar1 = var1 && (var1.baseOffset & 15) == 0;
  bool alignedVar2 = var2 && (var2.baseOffset & 15) == 0;
  void load(Expr src, string to, string scrap1 = null, string scrap2 = null) {
    if (auto addr = getAddr(af, src)) af.SSEOp("movaps", addr, to);
    else if (emitUnalignedAddr(af, src)) {
      af.popStack("%eax", 4);
      af.SSEOp("movups", "(%eax)", to);
    } else {
      // logln("src is ", (cast(Object) src).classinfo.name, ", ", src);
      src.emitAsm(af);
      if (scrap1 && scrap2 && false) {
        af.pushStack("%esp", 4);
        packLoad(to, scrap1, scrap2);
      } else {
        af.SSEOp("movaps", "(%esp)", to);
      }
      af.sfree(16);
    }
  }
  string srcOp = "%xmm1";
  if (alignedVar1 && alignedVar2) {
    var1.emitLocation(af);
    var2.emitLocation(af);
    /*packLoad("%xmm1", "%xmm0", "%xmm2");
    packLoad("%xmm0", "%xmm2", "%xmm3");*/
    af.popStack("%eax", 4);
    af.popStack("%edx", 4);
    af.SSEOp("movaps", "(%eax)", "%xmm1");
    af.SSEOp("movaps", "(%edx)", "%xmm0");
    af.salloc(16);
  }
  if (alignedVar1 && !alignedVar2) {
    af.salloc(12);
    var1.emitLocation(af);
    load(op2, "%xmm1", "%xmm2", "%xmm3");
    // logln("param 2 is ", op2, ", what to do .. ");
    packLoad("%xmm0", "%xmm2", "%xmm3");
    // af.popStack("%eax", 4);
    // af.SSEOp("movaps", "(%eax)", "%xmm0");
    af.salloc(4);
  }
  if (!alignedVar1 && alignedVar2) {
    af.salloc(12);
    var2.emitLocation(af);
    load(op1, "%xmm0", "%xmm2", "%xmm3");
    // logln("param 1 is ", op1, ", what to do .. ");
    packLoad("%xmm1", "%xmm2", "%xmm3");
    // af.popStack("%eax", 4);
    // af.SSEOp("movaps", "(%eax)", "%xmm1");
    af.salloc(4);
  }
  if (!alignedVar1 && !alignedVar2) {
    string prep1; bool prep1u;
    if (auto addr = getAddr(af, op1)) prep1 = addr;
    else if (emitUnalignedAddr(af, op1)) prep1u = true; // don't pop into register yet!!
    else op1.emitAsm(af);
    if (auto s = getAddr(af, op2)) srcOp = s;
    else if (emitUnalignedAddr(af, op2)) {
      if (prep1u) { af.sfree(8); emitUnalignedAddr(af, op2); } // resort
      af.popStack("%eax", 4);
      af.SSEOp("movups", "(%eax)", "%xmm1");
      if (prep1u) { emitUnalignedAddr(af, op1); }
    } else {
      // logln("op2 is ", (cast(Object) op2).classinfo.name, ", ", op2);
      if (prep1u) { af.sfree(4); } // force unload
      op2.emitAsm(af);
      af.SSEOp("movaps", "(%esp)", "%xmm1");
      af.sfree(16);
      if (prep1u) emitUnalignedAddr(af, op1); // reemit
    }
    if (prep1) af.SSEOp("movaps", prep1, "%xmm0");
    else if (prep1u) {
      af.popStack("%edx", 4);
      af.SSEOp("movups", "(%edx)", "%xmm0");
    } else {
      // logln("op1 is ", (cast(Object) op1).classinfo.name, ", ", op1);
      af.SSEOp("movaps", "(%esp)", "%xmm0");
      af.sfree(16);
    }
    af.salloc(16);
  }
  string sse;
  if (op == "+") sse = "addps";
  if (op == "-") sse = "subps";
  if (op == "*") sse = "mulps";
  if (op == "/") sse = "divps";
  if (op == "^") sse = "xorps";
  af.SSEOp(sse, srcOp, "%xmm0");
  // af.nvm("%xmm1"); // tend to get in the way
  af.SSEOp("movaps", "%xmm0", "(%esp)");
  // af.nvm("%xmm0"); // rarely helps
  mixin(mustOffset("-16"));
  if (auto lv = cast(LValue) res) {
    (new Assignment(lv, new Placeholder(op1.valueType()), false, true)).emitAsm(af);
  } else if (auto mv = cast(MValue) res) {
    mv.emitAssignment(af);
  } else fail;
  return true;
}

class Vec4fSmaller : Expr {
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
      if (vec4f != t1 || vec4f != t2) {
        logln("Fuck. ", t1, " or ", t2);
        fail;
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
      af.nvm("%edx");
      af.nvm("%eax");
      af.put("movmskps %xmm1, %eax");
      af.pushStack("%eax", 4);
    }
  }
}

import ast.vardecl, ast.assign;
class VecOp : Expr {
  IType type;
  int len, real_len;
  Expr ex1, ex2;
  string op;
  mixin defaultIterate!(ex1, ex2);
  mixin DefaultDup!();
  private this() { }
  this(IType it, int len, int real_len, Expr ex1, Expr ex2, string op) {
    this.type = it; this.len = len;
    this.ex1 = ex1; this.ex2 = ex2;
    this.op = op; this.real_len = real_len;
  }
  override {
    IType valueType() { return mkVec(type, len); }
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
        // logln("SSE vec op: ", ex1, ", ", ex2, " and ", op);
        // SSE needs no temps!
        if (!gotSSEVecOp(af, ex1, ex2, fastcast!(Expr) (var), op)) {
          auto filler1 = alignStackFor(t1, af); auto v1 = mkTemp(af, ex1, dg1);
          auto filler2 = alignStackFor(t2, af); auto v2 = mkTemp(af, ex2, dg2);
          for (int i = 0; i < len; ++i) {
            Expr l1 = v1, l2 = v2;
            if (e1v) l1 = getTupleEntries(reinterpret_cast(fastcast!(IType)~ e1v.asFilledTup, fastcast!(LValue)~ v1))[i];
            if (e2v) l2 = getTupleEntries(reinterpret_cast(fastcast!(IType)~ e2v.asFilledTup, fastcast!(LValue)~ v2))[i];
            (new Assignment(fastcast!(LValue)~ entries[i], lookupOp(op, l1, l2))).emitAsm(af);
          }
          for (int i = len; i < real_len; ++i) {
            (new Assignment(fastcast!(LValue)~ entries[i], new ZeroFiller(entries[i].valueType()))).emitAsm(af);
          }
          if (dg2) dg2(); af.sfree(filler2);
          if (dg1) dg1(); af.sfree(filler1);
        }
      });
    }
  }
}

class FailExpr : Expr {
  string mesg;
  IType typeMaybe;
  this(string s, IType tm = null) { this.mesg = s; typeMaybe = tm; }
  void fail() { logln("Fail: ", mesg); fail; }
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
    int len, real_len;
    if (v1v) { len = v1v.len; real_len = v1v.real_len; }
    else { len = v2v.len; real_len = v2v.real_len; }
    
    IType type;
    if (v1v is v2v && v1v == v2v) type = v1v.base;
    else {
      auto l1 = lhs; if (v1v) l1 = getTupleEntries(reinterpret_cast(v1v.asFilledTup, lhs))[0];
      auto r1 = rhs; if (v2v) r1 = getTupleEntries(reinterpret_cast(v2v.asFilledTup, rhs))[0];
      type = lookupOp(op, l1, r1).valueType();
    }
    return new VecOp(type, len, real_len, lhs, rhs, op);
  }
  Expr negate(Expr ex) {
    auto ty = resolveType(ex.valueType());
    // logln("negate? ", ty);
    auto vt = fastcast!(Vector)~ ty;
    if (!vt) return null;
    
    Expr[] list;
    foreach (ex2; getTupleEntries(reinterpret_cast(vt.asFilledTup, ex))[0 .. $-vt.extend]) {
      list ~= lookupOp("-", ex2);
    }
    if (vt.extend) list ~= new ZeroFiller(vt.base);
    return reinterpret_cast(vt, new StructLiteral(vt.asFilledTup.wrapped, list));
  }
  Expr handleVecEquals(Expr e1, Expr e2) {
    auto t1 = resolveType(e1.valueType()), t2 = resolveType(e2.valueType());
    auto v1 = fastcast!(Vector) (t1), v2 = fastcast!(Vector) (t2);
    if (!v1 || !v2 || v1 != v2) return null;
    Cond res;
    auto list1 = getTupleEntries(reinterpret_cast(v1.asFilledTup, e1))[0..v1.len];
    auto list2 = getTupleEntries(reinterpret_cast(v2.asFilledTup, e2))[0..v2.len];
    for (int i = 0; i < v1.len; ++i) {
      auto subcond = compare("==", list1[i], list2[i]);
      if (!res) res = subcond;
      else res = new BooleanOp!("&&")(res, subcond);
    }
    return new CondExpr(res);
  }
  Expr handleVecSmaller(Expr e1, Expr e2) {
    auto t1 = resolveType(e1.valueType()), t2 = resolveType(e2.valueType());
    auto v1 = fastcast!(Vector) (t1), v2 = fastcast!(Vector) (t2);
    if (!v1 || !v2) return null;
    if (v1.base != Single!(Float) || v1.len != 4) return null;
    if (v2.base != Single!(Float) || v2.len != 4) return null;
    
    return new Vec4fSmaller(e1, e2);
  }
  defineOp("-", &negate);
  defineOp("-", "-" /apply/ &handleVecOp);
  defineOp("+", "+" /apply/ &handleVecOp);
  defineOp("*", "*" /apply/ &handleVecOp);
  defineOp("/", "/" /apply/ &handleVecOp);
  defineOp("^", "^" /apply/ &handleVecOp);
  defineOp("%", "%" /apply/ &handleVecOp);
  defineOp("&", "&" /apply/ &handleVecOp);
  defineOp("|", "|" /apply/ &handleVecOp);
  defineOp("==", &handleVecEquals);
  defineOp("<", &handleVecSmaller);
  foldopt ~= delegate Itr(Itr it) {
    if (auto mae = fastcast!(MemberAccess_Expr) (it)) {
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
          return fastcast!(Itr) (lookupOp(vo.op, ex1, ex2));
        }
      }
    }
    return null;
  };
}

class XMM : MValue, Literal {
  int which;
  this(int w) { which = w; }
  mixin defaultIterate!();
  override {
    XMM dup() { return this; }
    IType valueType() { checkVecs(); return vec4f; }
    string getValue() { return qformat("%xmm", which); }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("16"));
      af.salloc(16);
      af.SSEOp("movaps", getValue(), "(%esp)");
    }
    void emitAssignment(AsmFile af) {
      mixin(mustOffset("-16"));
      af.SSEOp("movaps", "(%esp)", getValue());
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

Object gotMagnitude(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr >tree.expr.magnitude", &ex))
    return null;
  if (!t2.accept("|"))
    t2.failparse("Expected closing '|' for magnitude after ", ex);
  auto vt = resolveType(ex.valueType());
  if (auto v = fastcast!(Vector) (vt)) {
    text = t2;
    Statement init1, init2;
    Expr tmp = lvize(ex, &init1);
    tmp = lookupOp("*", tmp, tmp);
    tmp = lvize(tmp, &init2);
    auto strct = v.asStruct;
    tmp = fastcast!(Expr) (strct.lookupRel("sqrt_sum", reinterpret_cast(strct, tmp)));
    if (init2) tmp = new StatementAndExpr(init2, tmp);
    if (init1) tmp = new StatementAndExpr(init1, tmp);
    return fastcast!(Object) (tmp);
  }
  t2.failparse("Invalid type for magnitude: ", vt);
}
mixin DefaultParser!(gotMagnitude, "tree.expr.magnitude", "24064", "|");
