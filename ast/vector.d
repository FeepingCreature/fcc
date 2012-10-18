module ast.vector;

import
  ast.base, ast.tuples, ast.tuple_access, ast.types, ast.fold,
  ast.fun, ast.funcall, ast.aliasing, ast.conditionals,
  ast.structure, ast.namespace, ast.modules, ast.structfuns, ast.returns;

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
    todo(qformat("what is alignment of ", base));
    // if (base.size < 4 || len < 3) return 4;
    return 16;
  }
  override bool isPointerLess() { return base.isPointerLess(); }
  // quietly treat n-size as n+1-size
  bool extend() { return len == 3 && (Single!(Float) == base || Single!(SysInt) == base || Single!(Double) == base); }
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
    string mangle() { return qformat("vec_"[], len, "_"[], base.mangle()); }
    string toString() { return qformat("vec("[], base, ", "[], len, ")"[]); }
    bool isTempNamespace() { return false; }
    string llvmType() {
      return qformat("<", real_len(), " x ", typeToLLVM(base), ">"); 
    }
    string llvmSize() {
      return asFilledTup.llvmSize();
    }
    int opEquals(IType it) {
      auto vec = fastcast!(Vector) (resolveType(it));
      if (!vec) return false;
      return vec.base == base && vec.len == len;
    }
    Object lookupRel(string str, Expr base, bool isDirectLookup = true) {
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
      // if (auto res = getSSESwizzle(this, base, str)) return fastcast!(Object) (res);
      Expr generate(Expr ex) {
        if (str.length == 1) {
          auto ch = str[0];
          if (ch == 'x') return mkTupleIndexAccess(ex, 0);
          if (ch == 'y') return mkTupleIndexAccess(ex, 1);
          if (ch == 'z') return mkTupleIndexAccess(ex, 2);
          if (ch == 'w') return mkTupleIndexAccess(ex, 3);
          assert(false);
        }
        auto parts = getTupleEntries(ex, null, true);
        Expr[] exprs;
        foreach (ch; str) {
              if (ch == 'x') exprs ~= parts[0];
          else if (ch == 'y') exprs ~= parts[1];
          else if (ch == 'z') exprs ~= parts[2];
          else if (ch == 'w') exprs ~= parts[3];
          else assert(false);
        }
        if (exprs.length == 1) return exprs[0];
        if (exprs.length > 4) throw new Exception("Cannot use swizzle to create vector larger than four elements");
        auto new_vec = mkVec(this.base, exprs.length);
        if (new_vec.extend) exprs ~= fastalloc!(ZeroInitializer)(this.base);
        return reinterpret_cast(new_vec, mkTupleExpr(exprs));
      }
      // no need for caching in this case
      if (str.length == 1) {
        return fastcast!(Object) (generate(reinterpret_cast(asFilledTup, base)));
      }
      if (auto lv = fastcast!(LValue) (base)) {
        return fastcast!(Object)~ tmpize_maybe(fastalloc!(RefExpr)(lv), (Expr ex) {
          return generate(fastalloc!(DerefExpr)(reinterpret_cast(fastalloc!(Pointer)(asFilledTup), ex)));
        });
      }
      return fastcast!(Object)~tmpize_maybe(reinterpret_cast(asFilledTup, base), &generate);
    }
  }
}

class SSESwizzle : Expr {
  Expr sup;
  string rule;
  IType type;
  this(Expr e, IType t, string r) {
    sup = e;
    type = t;
    rule = r;
    if (sup.valueType().llvmType() != type.llvmType()) {
      logln("sup ", sup, ", type ", type, ". ");
      fail;
    }
  }
  private this() { }
  mixin defaultIterate!(sup);
  mixin DefaultDup!();
  override {
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      todo("SSESwizzle::emitLLVM");
      /*int mask;
      foreach_reverse (ch; rule) switch (ch) {
        case 'x': mask = mask*4 + 0; break;
        case 'y': mask = mask*4 + 1; break;
        case 'z': mask = mask*4 + 2; break;
        case 'w': mask = mask*4 + 3; break;
      }
      if (auto cv = fastcast!(CValue) (sup)) {
        cv.emitLocation(lf);
        lf.popStack("%eax", 4);
        lf.SSEOp("movups", "(%eax)", "%xmm0");
        lf.nvm("%eax");
        lf.salloc(16);
      } else {
        sup.emitLLVM(lf);
        lf.SSEOp("movaps", "(%esp)", "%xmm0");
      }
      lf.SSEOp(qformat("shufps $"[], mask, ", "[]), "%xmm0"[], "%xmm0"[]);
      lf.SSEOp("movaps", "%xmm0", "(%esp)");*/
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
  return fastalloc!(SSESwizzle)(ex, v2, rule);
}

class SSEIntToFloat : Expr {
  Expr base;
  this(Expr b) { base = b; }
  mixin defaultIterate!(base);
  SSEIntToFloat dup() { return fastalloc!(SSEIntToFloat)(base.dup()); }
  override {
    IType valueType() { checkVecs(); return vec3f; }
    void emitLLVM(LLVMFile lf) {
      todo("SSEIntToFloat::emitLLVM");
      /*base.emitLLVM(lf);
      lf.SSEOp("cvtdq2ps", "(%esp)", "%xmm0");
      lf.SSEOp("movaps", "%xmm0", "(%esp)");*/
    }
  }
}

class MultiplesExpr : Expr {
  Expr base;
  Vector type;
  int vecsize;
  this(Expr b, int sz) {
    this.base = b;
    this.vecsize = sz;
    this.type = fastalloc!(Vector)(b.valueType(), sz);
  }
  mixin defaultIterate!(base);
  override {
    MultiplesExpr dup() { return fastalloc!(MultiplesExpr)(base.dup, vecsize); }
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      auto b = save(lf, base);
      string bs = typeToLLVM(base.valueType());
      string ms = typeToLLVM(valueType());
      string res = "undef";
      for (int i = 0; i < vecsize; ++i) {
        res = save(lf, "insertelement ", ms, " ", res, ", ", bs, " ", b, ", i32 ", i);
      }
      push(lf, res);
    }
  }
}

import ast.literals;
class AlignedVec4Literal : Expr, Literal {
  string id;
  IType type;
  FloatExpr base; int len;
  this(IType t, FloatExpr fe, int l) { type = t; base = fe; len = l; }
  string getID(LLVMFile lf) {
    todo("AlignedVec4Literal::getId");
    /*if (!id) {
      float[4] meep;
      foreach (ref v; meep) v = base.f;
      id = lf.allocConstant(Format("__vec_constant_"[], lf.constants.length), cast(ubyte[]) meep.dup);
    }*/
    return id;
  }
  override {
    string toString() { return qformat(type, " (", base, " x ", len, ")"); }
    mixin defaultIterate!(base);
    typeof(this) dup() { return new typeof(this) (type, base, len); }
    IType valueType() { return type; }
    string getValue() { assert(false, "Use getID instead! "); }
    void emitLLVM(LLVMFile lf) {
      // lf.put("#avlit of "[], type, " * "[], len);
      string[] parts;
      string bs = typeToLLVM(base.valueType());
      for (int i = 0; i < len; ++i) {
        parts ~= bs;
        parts ~= save(lf, base);
      }
      formTuple(lf, parts);
    }
  }
}

static this() {
  // probably not safe due to differing alignment
  /*foldopt ~= delegate Itr(Itr it) {
    auto me = fastcast!(MultiplesExpr) (it);
    if (!me) return null;
    bool canDup; // no side effects
    auto fbase = me.base;
    if (auto lt = fastcast!(Literal) (fbase)) {
      if (me.vecsize == 3 || me.vecsize == 4) if (auto fe = fastcast!(FloatExpr) (lt)) {
        return fastalloc!(AlignedVec4Literal)(me.type, fe, me.vecsize);
      }
      canDup = true;
    }
    if (auto var = fastcast!(Variable) (fbase)) canDup = true;
    if (!canDup) {
      // logln("me of ", me.base);
      return null;
    }
    Expr[] list;
    for (int i = 0; i < me.vecsize; ++i) list ~= fbase;
    return fastcast!(Itr) (reinterpret_cast(me.type, mkTupleExpr(list)));
  };*/
  foldopt ~= delegate Itr(Itr it) {
    auto mae = fastcast!(MemberAccess_Expr) (it);
    if (!mae) return null;
    auto rce = fastcast!(RCE) (mae.base);
    if (!rce) return null;
    auto fe = rce.from;
    auto mult = fastcast!(MultiplesExpr) (fe);
    auto avlit = fastcast!(AlignedVec4Literal) (fe);
    if (!mult && !avlit) return null;
    IType basetype; Expr res;
    if (mult) { basetype = mult.base.valueType(); res = mult.base; }
    if (avlit) { basetype = avlit.base.valueType(); res = avlit.base; }
    if (basetype != mae.stm.type) {
      /*logln("type mismatch: accessing ", mae.stm.type, " from set of ",
        basetype);
      logln("mae ", mae);
      logln("rce ", rce);
      fail;*/
      return null;
    }
    return fastcast!(Iterable) (res);
  };
}

Object constructVector(Expr base, Vector vec, bool allowCastVecTest = true, bool canfail = false) {
  auto ex2 = base;
  if (allowCastVecTest && gotImplicitCast(ex2, (IType it) { return test(it == vec.base); })) {
    return fastalloc!(MultiplesExpr)(ex2, vec.len);
  }
  checkVecs();
  if (vec == vec3f && base.valueType() == vec3i) {
    return fastalloc!(SSEIntToFloat)(base);
  }
  opt(base);
  return fastcast!(Object)~ tmpize_maybe(base, delegate Expr(Expr base) {
    Expr[] exs;
    bool failed;
    void decompose(Expr ex) {
      auto ex2 = ex;
      if (gotImplicitCast(ex2, (IType it) { return test(it == vec.base); })) {
        exs ~= ex2;
        if (exs.length > vec.len) {
          if (canfail) { failed = true; return; }
          else throw new Exception(Format("Extraneous argument to ", vec, " constructor: ", exs[$-1]));
        }
        return;
      }
      auto tup = fastcast!(Tuple) (base.valueType());
      ex2 = ex;
      if (gotImplicitCast(ex2, Single!(HintType!(Tuple)), (IType it) { return !!fastcast!(Tuple) (it); })) {
        foreach (entry; getTupleEntries(ex2)) { decompose(entry); if (failed) break; }
        return;
      }
      if (canfail) { failed = true; return; }
      else throw new Exception(Format("Unexpected type in ", vec, " constructor: ", ex.valueType()));
    }
    
    decompose(base);
    if (failed) return null;
    
    if (exs.length < vec.len) {
      if (canfail) return null;
      else throw new Exception(Format("Insufficient values for ", vec, " constructor"));
    }
    
    if (vec.extend) exs ~= fastalloc!(ZeroInitializer)(vec.base);
    return reinterpret_cast(vec, fastalloc!(StructLiteral)(vec.asStruct, exs));
  });
  if (canfail) return null;
  assert(false);
}

Object gotVecConstructor(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType ty;
  if (t2.accept("\"") || t2.accept("[") || t2.accept("(")) return null;
  if (!rest(t2, "type"[], &ty)) {
    // logln("fail 1 @", t2.mystripl().nextText());
    return null;
  }
  if (t2.accept(".")) return null; // vec.XYZ
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
    FastVec3Sum dup() { return fastalloc!(FastVec3Sum)(base.dup); }
    IType valueType() { return Single!(Float); }
    void emitLLVM(LLVMFile lf) {
      auto bv = save(lf, base);
      auto bt = typeToLLVM(base.valueType());
      auto v0 = save(lf, "extractelement ", bt, " ", bv, ", i32 0");
      auto v1 = save(lf, "extractelement ", bt, " ", bv, ", i32 1");
      auto v2 = save(lf, "extractelement ", bt, " ", bv, ", i32 2");
      auto res = v0;
      res = save(lf, "fadd float ", res, ", ", v1);
      res = save(lf, "fadd float ", res, ", ", v2);
      push(lf, res);
    }
  }
}

class FastVec3Norm : Expr {
  Expr base; IType vec;
  this(Expr b, IType v) { base = b; vec = v; }
  override {
    mixin defaultIterate!(base);
    FastVec3Norm dup() { return fastalloc!(FastVec3Norm)(base.dup, vec); }
    IType valueType() { return vec; }
    void emitLLVM(LLVMFile lf) {
      auto b2 = base;
      logln("FROM: ", base);
      opt(b2);
      logln("  TO: ", b2);
      auto bv = save(lf, base);
      auto bt = typeToLLVM(base.valueType());
      // logln("emit ", base, " being ", base.valueType());
      auto sqv = save(lf, "fmul ", bt, " ", bv, ", ", bv);
      string sum;
      {
        auto v0 = save(lf, "extractelement ", bt, " ", sqv, ", i32 0");
        auto v1 = save(lf, "extractelement ", bt, " ", sqv, ", i32 1");
        auto v2 = save(lf, "extractelement ", bt, " ", sqv, ", i32 2");
        sum = v0;
        sum = save(lf, "fadd float ", sum, ", ", v1);
        sum = save(lf, "fadd float ", sum, ", ", v2);
      }
      // see bottom of ast.math
      if (once(lf, "intrinsic llvm.sqrt.f32")) {
        lf.decls["llvm.sqrt.f32"] = qformat("declare float @llvm.sqrt.f32 (float)");
      }
      auto root = save(lf, "call float @llvm.sqrt.f32(float ", sum, ")");
      string vec = "undef";
      vec = save(lf, "insertelement <4 x float> ", vec, ", float ", root, ", i32 0");
      vec = save(lf, "insertelement <4 x float> ", vec, ", float ", root, ", i32 1");
      vec = save(lf, "insertelement <4 x float> ", vec, ", float ", root, ", i32 2");
      vec = save(lf, "insertelement <4 x float> ", vec, ", float 1.0, i32 3");
      load(lf, "fdiv <4 x float> ", bv, ", ", vec);
    }
  }
}

const letters = "xyzw";

import ast.templ, ast.math;
Stuple!(Structure, Vector, Module)[] cache;
Structure mkVecStruct(Vector vec) {
  foreach (entry; cache) if (entry._2.isValid && entry._1 == vec) return entry._0;
  auto res = fastalloc!(Structure)(cast(string) null);
  res.isTempStruct = true;
  res.sup = sysmod;
  auto backup = namespace();
  namespace.set(res);
  scope(exit) namespace.set(backup);
  for (int i = 0; i < vec.len; ++i)
    fastalloc!(RelMember)([letters[i]], vec.base, res);
  
  if (vec.extend)
    fastalloc!(RelMember)(cast(string) null, vec.base, res);
  
  res.add(fastalloc!(RelMember)("self"[], vec, 0));
  
  Expr sqr(Expr ex) { return lookupOp("*", ex, ex); }
  
  {
    Expr lensq = sqr(fastcast!(Expr)~ res.lookup("x"));
    for (int i = 1; i < vec.len; ++i)
      lensq = lookupOp("+", lensq, sqr(fastcast!(Expr)~ res.lookup([letters[i]])));
    res.add(fastalloc!(ExprAlias)(lensq, "lensq"[]));
    res.add(fastalloc!(ExprAlias)(lensq, "selfdot"[]));
  }
  
  {
    Expr sum;
    if (false && vec.len == 3 && Single!(Float) == vec.base) {
      sum = fastalloc!(FastVec3Sum)(fastcast!(Expr) (res.lookup("self")));
    } else {
      sum = fastcast!(Expr)~ res.lookup("x");
      for (int i = 1; i < vec.len; ++i)
        sum = lookupOp("+", sum, fastcast!(Expr)~ res.lookup([letters[i]]));
    }
    res.add(fastalloc!(ExprAlias)(sum, "sum"[]));
  }
  
  res.add(fastalloc!(TypeAlias)(vec.base, "base"[]));
  // auto vv = fastalloc!(RelMember)("vec"[], vec, 0);
  // res.add(fastalloc!(ExprAlias)(reinterpret_cast(vec, fastcast!(Expr) (vv)), "vec"[]));
  
  {
    Expr lensq = fastcast!(Expr)~ res.lookup("lensq");
    IType lvt = lensq.valueType();
    Expr sum = fastcast!(Expr) (res.lookup("sum"));
    Expr len;
    Expr weirdlen;
    if (Single!(Float) == lvt || Single!(SysInt) == lvt) {
      len = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("C_sqrtf"), lensq, "sqrtf"
      );
      weirdlen = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("C_sqrtf"), sum, "sqrtf"
      );
    } else if (Single!(Double) == lvt || Single!(Long) == lvt) {
      auto mylensq = lensq, mysum = sum;
      if (Single!(Long) == mylensq.valueType()) {
        mylensq = fastalloc!(LongAsDouble)(mylensq);
        mysum = fastalloc!(LongAsDouble)(mysum);
      }
      len = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("C_sqrt"), mylensq, "sqrt"
      );
      weirdlen = buildFunCall(
        fastcast!(Function)~ sysmod.lookup("C_sqrt"), mysum, "sqrt"
      );
    }
    res.add(fastalloc!(ExprAlias)(fastalloc!(FastVec3Norm)(fastcast!(Expr) (res.lookup("self")), vec), "normalized"[]));
    if (!len) logln("Can't add length for ", lensq.valueType());
    assert(!!len);
    assert(!!weirdlen);
    res.add(fastalloc!(ExprAlias)(len, "magnitude"[]));
    res.add(fastalloc!(ExprAlias)(weirdlen, "sqrt_sum"[]));
  }

  cache ~= stuple(res, vec, fastcast!(Module) (current_module()));
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
      return reinterpret_cast(fastalloc!(StaticArray)(vec.base, vec.real_len()), ex);
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
        Expr generate(Expr ex) {
          auto entries = getTupleEntries(ex, null, true);
          assert(entries.length == 4);
          return mkTupleExpr(entries[0], entries[1], entries[2]);
        }
        if (auto lv = fastcast!(LValue) (ex))
          return tmpize_maybe(fastalloc!(RefExpr)(lv), (Expr ex) {
            return generate(fastalloc!(DerefExpr)(reinterpret_cast(fastalloc!(Pointer)(vec.asFilledTup), ex)));
          });
        auto filled = reinterpret_cast(vec.asFilledTup, ex);
        return tmpize_maybe(filled, &generate);
      } else
        return reinterpret_cast(vec.asTup, ex);
    }
    return null;
  };
  // veci to vecf
  implicits ~= delegate Expr(Expr ex) {
    auto vec = fastcast!(Vector) (resolveType(ex.valueType()));
    if (!vec) return null;
    if (!fastcast!(SysInt) (resolveType(vec.base))) return null;
    auto to = fastalloc!(Vector)(Single!(Float), vec.len);
    return fastcast!(Expr) (constructVector(mkTupleValueExpr(getTupleEntries(reinterpret_cast(vec.asFilledTup, ex), null, true)[0..vec.len]), to, false));
  };
  // tuple to vec, if demanded
  implicits ~= delegate void(Expr ex, IType dest, void delegate(Expr) dg) {
    if (auto vec = fastcast!(Vector) (resolveType(dest))) {
      auto exvt = ex.valueType();
      if (auto tup = fastcast!(Tuple) (exvt)) {
        if (auto res = fastcast!(Expr) (constructVector(ex, vec, true, true))) {
          dg(res);
          return;
        }
      }
    }
    return;
  };
}

import ast.parse, ast.int_literal;
Object gotVecType(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType it;
  Expr len;
  if (!t2.accept("(")) return null;
  if (!rest(t2, "type"[], &it) ||
      !t2.accept(",") ||
      !rest(t2, "tree.expr"[], &len) ||
      !t2.accept(")"[]))
    t2.failparse("Fail to parse vector"[]);
  auto ie = fastcast!(IntExpr)~ fold(len);
  if (!ie)
    text.failparse("Size parameter to vec not foldable or int"[]);
  text = t2;
  return mkVec(it, ie.num);
}
mixin DefaultParser!(gotVecType, "type.vector"[], "34"[], "vec"[]);

bool pretransform(ref Expr ex, ref IType it) {
  it = resolveType(it);
  if (auto tup = fastcast!(Tuple)~ it) {
    if (tup.types.length == 1) {
      ex = reinterpret_cast(tup.types[0], ex);
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
  auto res = fastalloc!(Vector)(base, len);
  vec_cache[tup] = res;
  return res;
}

Vector vec3f, vec4f, vec3i;
void checkVecs() {
  if (!vec3f) vec3f = mkVec(Single!(Float), 3);
  if (!vec4f) vec4f = mkVec(Single!(Float), 4);
  if (!vec3i) vec3i = mkVec(Single!(SysInt), 3);
}

string getAddr(LLVMFile lf, Expr src) {
  if (auto rce = fastcast!(RCE) (src)) src = rce.from; // immaterial
  if (auto lit = fastcast!(AlignedVec4Literal) (src)) return lit.getID(lf);
  else return null;
}

bool emitUnalignedAddr(LLVMFile lf, Expr src, ref bool wasAligned) {
  wasAligned = false;
  if (auto cv = fastcast!(CValue) (src)) {
    if (auto var = fastcast!(Variable) (cv)) {
      todo(qformat("wat.. emitUnalignedAddr ", src));
      /*auto offs = var.baseOffset;
      while (offs < 0) offs += 16;
      if (offs % 16 == 0) wasAligned = true;*/
    }
    cv.emitLocation(lf);
    return true;
  } else return false;
}

bool gotSSEVecOp(LLVMFile lf, Expr op1, Expr op2, Expr res, string op) {
  todo("gotSSEVecOp");
  return false;
  /*mixin(mustOffset("0"[]));
  checkVecs;
  if (op1.valueType() != vec3f && op1.valueType() != vec4f
   || op2.valueType() != vec3f && op2.valueType() != vec4f
   || op1.valueType() != op2.valueType())
    return false;
  if (op != "+"[] /or/ "-"[] /or/ "*"[] /or/ "/"[] /or/ "^"[]) return false;
  void packLoad(string dest, string scrap1, string scrap2) {
    lf.popStack("%eax"[], 4);
    // lf.SSEOp("movaps"[], "(%eax)"[], dest);
    // recommended by the intel core opt manual, 3-50
    // also benchmarked and YES it's faster .. IFF there's a dependency.
    lf.movd("(%eax)"[], dest);
    lf.movd("8(%eax)"[], scrap1);
    lf.SSEOp("punpckldq"[], scrap1, dest); // can't do directly! punpckldq requires alignment; movd doesn't.
    lf.movd("4(%eax)"[], scrap1);
    lf.movd("12(%eax)"[], scrap2);
    lf.SSEOp("punpckldq"[], scrap2, scrap1);
    lf.SSEOp("punpckldq"[], scrap1, dest);
  }
  auto var1 = fastcast!(Variable) (op1), var2 = fastcast!(Variable) (op2);
  bool alignedVar1 = var1 && ((var1.baseOffset - esp_alignment_delta) & 15) == 0;
  bool alignedVar2 = var2 && ((var2.baseOffset - esp_alignment_delta) & 15) == 0;
  void load(Expr src, string to, string scrap1 = null, string scrap2 = null) {
    bool wasAligned;
    if (auto addr = getAddr(lf, src)) lf.SSEOp("movaps"[], addr, to);
    else if (emitUnalignedAddr(lf, src, wasAligned)) {
      lf.popStack("%eax"[], 4);
      lf.SSEOp(wasAligned?"movaps"[]:"movups"[], "(%eax)"[], to);
    } else {
      // logln("src is "[], (cast(Object) src).classinfo.name, ", "[], src);
      src.emitLLVM(lf);
      if (scrap1 && scrap2 && false) {
        lf.pushStack("%esp"[], 4);
        packLoad(to, scrap1, scrap2);
      } else {
        lf.SSEOp("movaps", "(%esp)", to);
      }
      lf.sfree(16);
    }
  }
  string srcOp = "%xmm1";
  if (alignedVar1 && alignedVar2) {
    var1.emitLocation(lf);
    var2.emitLocation(lf);
    /+packLoad("%xmm1"[], "%xmm0"[], "%xmm2"[]);
    packLoad("%xmm0"[], "%xmm2"[], "%xmm3"[]);+/
    lf.popStack("%eax"[], 4);
    lf.popStack("%edx"[], 4);
    lf.SSEOp("movaps"[], "(%eax)"[], "%xmm1"[]);
    lf.SSEOp("movaps"[], "(%edx)"[], "%xmm0"[]);
    lf.salloc(16);
  }
  if (alignedVar1 && !alignedVar2) {
    lf.salloc(12);
    var1.emitLocation(lf);
    load(op2, "%xmm1"[], "%xmm2"[], "%xmm3"[]);
    // logln("param 2 is "[], op2, "[], what to do .. "[]);
    packLoad("%xmm0"[], "%xmm2"[], "%xmm3"[]);
    // lf.popStack("%eax"[], 4);
    // lf.SSEOp("movaps"[], "(%eax)"[], "%xmm0"[]);
    lf.salloc(4);
  }
  if (!alignedVar1 && alignedVar2) {
    lf.salloc(12);
    var2.emitLocation(lf);
    load(op1, "%xmm0"[], "%xmm2"[], "%xmm3"[]);
    // logln("param 1 is "[], op1, "[], what to do .. "[]);
    packLoad("%xmm1"[], "%xmm2"[], "%xmm3"[]);
    // lf.popStack("%eax"[], 4);
    // lf.SSEOp("movaps"[], "(%eax)"[], "%xmm1"[]);
    lf.salloc(4);
  }
  if (!alignedVar1 && !alignedVar2) {
    string prep1; bool prep1u, prep1u_align;
    if (auto addr = getAddr(lf, op1)) prep1 = addr;
    else if (emitUnalignedAddr(lf, op1, prep1u_align)) prep1u = true; // don't pop into register yet!!
    else op1.emitLLVM(lf);
    bool wasAligned;
    if (auto s = getAddr(lf, op2)) srcOp = s;
    else if (emitUnalignedAddr(lf, op2, wasAligned)) {
      if (prep1u) { lf.sfree(8); emitUnalignedAddr(lf, op2, wasAligned); } // resort
      lf.popStack("%eax"[], 4);
      lf.SSEOp(wasAligned?"movaps"[]:"movups"[], "(%eax)"[], "%xmm1"[]);
      if (prep1u) { emitUnalignedAddr(lf, op1, prep1u_align); }
    } else {
      // logln("op2 is "[], (cast(Object) op2).classinfo.name, ", "[], op2);
      if (prep1u) { lf.sfree(4); } // force unload
      op2.emitLLVM(lf);
      lf.SSEOp("movaps"[], "(%esp)"[], "%xmm1"[]);
      lf.sfree(16);
      if (prep1u) emitUnalignedAddr(lf, op1, prep1u_align); // reemit
    }
    if (prep1) lf.SSEOp("movaps"[], prep1, "%xmm0"[]);
    else if (prep1u) {
      lf.popStack("%edx"[], 4);
      lf.SSEOp(prep1u_align?"movaps"[]:"movups"[], "(%edx)"[], "%xmm0"[]);
    } else {
      // logln("op1 is "[], (cast(Object) op1).classinfo.name, ", "[], op1);
      lf.SSEOp("movaps"[], "(%esp)"[], "%xmm0"[]);
      lf.sfree(16);
    }
    lf.salloc(16);
  }
  string sse;
  if (op == "+"[]) sse = "addps";
  if (op == "-"[]) sse = "subps";
  if (op == "*"[]) sse = "mulps";
  if (op == "/"[]) sse = "divps";
  if (op == "^"[]) sse = "xorps";
  lf.SSEOp(sse, srcOp, "%xmm0"[]);
  // lf.nvm("%xmm1"[]); // tend to get in the way
  lf.SSEOp("movaps"[], "%xmm0"[], "(%esp)"[]);
  // lf.nvm("%xmm0"[]); // rarely helps
  mixin(mustOffset("-16"[]));
  if (auto lv = cast(LValue) res) {
    emitAssign(lf, lv, fastalloc!(Placeholder)(op1.valueType()), false, true);
  } else if (auto mv = cast(MValue) res) {
    mv.emitAssignment(lf);
  } else fail;
  return true;*/
}

class Vec4fSmaller : Expr {
  Expr ex1, ex2;
  this(Expr e1, Expr e2) { this.ex1 = e1; this.ex2 = e2; }
  mixin defaultIterate!(ex1, ex2);
  mixin DefaultDup!();
  private this() { }
  override {
    IType valueType() { return Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      checkVecs();
      auto t1 = fastcast!(Vector)(resolveType(ex1.valueType())), t2 = ex2.valueType();
      if (vec4f != t1 || vec4f != t2) {
        logln("Fuck. "[], t1, " or "[], t2);
        fail;
      }
      auto vectype = qformat("<", t1.len, " x ", typeToLLVM(t1.base), ">");
      
      ex1.emitLLVM(lf);
      // llcast(lf, typeToLLVM(t1), vectype, lf.pop(), t1.llvmSize());
      auto s1 = lf.pop();
      
      ex2.emitLLVM(lf);
      // llcast(lf, typeToLLVM(t1), vectype, lf.pop(), t1.llvmSize());
      auto s2 = lf.pop();
      
      auto cmp = save(lf, "fcmp olt ", vectype, " ", s1, ", ", s2);
      string getbit(int i) {
        return save(lf, "zext i1 ",
          save(lf, "extractelement <4 x i1> ", cmp, ", i32 ", i),
          " to i32");
      }
      auto res = getbit(0);
      res = save(lf, "or i32 ", res, ", ", save(lf, "shl i32 ", getbit(1), ", 1"));
      res = save(lf, "or i32 ", res, ", ", save(lf, "shl i32 ", getbit(2), ", 2"));
      res = save(lf, "or i32 ", res, ", ", save(lf, "shl i32 ", getbit(3), ", 3"));
      lf.push(res);
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
    string toString() { return Format("("[], ex1, " "[], op, " "[], ex2, ")"[]); }
    IType valueType() { return mkVec(type, len); }
    void emitLLVM(LLVMFile lf) {
      auto t1 = ex1.valueType(), t2 = ex2.valueType();
      while (pretransform(ex1, t1) || pretransform(ex2, t2)) { }
      auto e1v = fastcast!(Vector)~ t1, e2v = fastcast!(Vector)~ t2;
      
      auto var = fastalloc!(LLVMRef)(valueType());
      var.allocate(lf);
      var.begin(lf);
      scope(success) var.end(lf);
      
      scope(success) var.emitLLVM(lf);
      
      auto entries = getTupleEntries(
        reinterpret_cast(
          fastcast!(IType)~ (fastcast!(Vector)~ valueType()).asFilledTup,
          fastcast!(LValue)~ var
      ), null, true);
      void delegate() dg1, dg2;
      mixin(mustOffset("0"));
      // logln("SSE vec op: "[], ex1, ", "[], ex2, " and "[], op);
      // SSE needs no temps!
      if (true || !gotSSEVecOp(lf, ex1, ex2, fastcast!(Expr) (var), op)) {
        /*auto filler1 = alignStackFor(t1, lf); */auto v1 = mkTemp(lf, ex1, dg1);
        /*auto filler2 = alignStackFor(t2, lf); */auto v2 = mkTemp(lf, ex2, dg2);
        for (int i = 0; i < len; ++i) {
          Expr l1 = v1, l2 = v2;
          if (e1v) l1 = getTupleEntries(reinterpret_cast(fastcast!(IType)~ e1v.asFilledTup, fastcast!(LValue)~ v1), null, true)[i];
          if (e2v) l2 = getTupleEntries(reinterpret_cast(fastcast!(IType)~ e2v.asFilledTup, fastcast!(LValue)~ v2), null, true)[i];
          emitAssign(lf, fastcast!(LValue) (entries[i]), lookupOp(op, l1, l2));
        }
        for (int i = len; i < real_len; ++i) {
          emitAssign(lf, fastcast!(LValue) (entries[i]), fastalloc!(ZeroInitializer)(entries[i].valueType()));
        }
        if (dg2) dg2(); // lf.sfree(filler2);
        if (dg1) dg1(); // lf.sfree(filler1);
      }
    }
  }
}

class FailExpr : Expr {
  string mesg;
  IType typeMaybe;
  this(string s, IType tm = null) { this.mesg = s; typeMaybe = tm; }
  void fail() { logln("Fail: "[], mesg); fail; }
  override {
    IType valueType() { if (typeMaybe) return typeMaybe; fail(); return null; }
    void emitLLVM(LLVMFile lf) { fail(); }
    mixin defaultIterate!();
    FailExpr dup() { return this; }
  }
}

import ast.opers, ast.aggregate;
static this() {
  Expr handleVecOp(string op, Expr lhs, Expr rhs) {
    auto v1 = lhs.valueType(), v2 = rhs.valueType();
    while (pretransform(lhs, v1) || pretransform(rhs, v2)) { }
    
    auto v1v = fastcast!(Vector)~ v1, v2v = fastcast!(Vector)~ v2;
    if (!v1v && !v2v) return null;
    
    if (v1v && v2v && v1v.asTup.types.length != v2v.asTup.types.length)
      throw new Exception(Format("Mismatching tuple types: "[], v1v, " and "[], v2v));
    int len, real_len;
    if (v1v) { len = v1v.len; real_len = v1v.real_len; }
    else { len = v2v.len; real_len = v2v.real_len; }
    
    IType type;
    if (v1v is v2v && v1v == v2v) type = v1v.base;
    else {
      auto l1 = lhs; if (v1v) l1 = getTupleEntries(reinterpret_cast(v1v.asFilledTup, lhs), null, true)[0];
      auto r1 = rhs; if (v2v) r1 = getTupleEntries(reinterpret_cast(v2v.asFilledTup, rhs), null, true)[0];
      type = lookupOp(op, l1, r1).valueType();
    }
    return fastalloc!(VecOp)(type, len, real_len, lhs, rhs, op);
  }
  Expr negate(Expr ex) {
    auto ty = resolveType(ex.valueType());
    // logln("negate? "[], ty);
    auto vt = fastcast!(Vector)~ ty;
    if (!vt) return null;
    
    Expr[] list;
    foreach (ex2; getTupleEntries(reinterpret_cast(vt.asFilledTup, ex))[0 .. $-vt.extend]) {
      list ~= lookupOp("-"[], ex2);
    }
    if (vt.extend) list ~= fastalloc!(ZeroInitializer)(vt.base);
    return reinterpret_cast(vt, fastalloc!(StructLiteral)(vt.asFilledTup.wrapped, list));
  }
  Expr handleVecEquals(Expr e1, Expr e2) {
    auto t1 = resolveType(e1.valueType()), t2 = resolveType(e2.valueType());
    auto v1 = fastcast!(Vector) (t1), v2 = fastcast!(Vector) (t2);
    if (!v1 || !v2 || v1 != v2) return null;
    Cond res;
    auto list1 = getTupleEntries(reinterpret_cast(v1.asFilledTup, e1))[0..v1.len];
    auto list2 = getTupleEntries(reinterpret_cast(v2.asFilledTup, e2))[0..v2.len];
    for (int i = 0; i < v1.len; ++i) {
      auto subcond = compare("=="[], list1[i], list2[i]);
      if (!res) res = subcond;
      else res = new BooleanOp!("&&"[])(res, subcond);
    }
    return fastalloc!(CondExpr)(res);
  }
  Expr handleVecSmaller(Expr e1, Expr e2) {
    auto t1 = resolveType(e1.valueType()), t2 = resolveType(e2.valueType());
    auto v1 = fastcast!(Vector) (t1), v2 = fastcast!(Vector) (t2);
    if (!v1 || !v2) return null;
    if (v1.base != Single!(Float) || v1.len != 4) return null;
    if (v2.base != Single!(Float) || v2.len != 4) return null;
    
    return fastalloc!(Vec4fSmaller)(e1, e2);
  }
  defineOp("-"[], &negate);
  defineOp("-"[], "-" /apply/ &handleVecOp);
  defineOp("+"[], "+" /apply/ &handleVecOp);
  defineOp("*"[], "*" /apply/ &handleVecOp);
  defineOp("/"[], "/" /apply/ &handleVecOp);
  defineOp("^"[], "^" /apply/ &handleVecOp);
  defineOp("%"[], "%" /apply/ &handleVecOp);
  defineOp("&"[], "&" /apply/ &handleVecOp);
  defineOp("|"[], "|" /apply/ &handleVecOp);
  defineOp("=="[], &handleVecEquals);
  defineOp("<"[], &handleVecSmaller);
  /*foldopt ~= delegate Itr(Itr it) {
    if (auto mae = fastcast!(MemberAccess_Expr) (it)) {
      auto base = mae.base;
      if (auto rce = fastcast!(RCE) (base)) {
        if (auto vo = fastcast!(VecOp) (rce.from)) {
          assert(mae.stm.offset % vo.type.size() == 0);
          auto id = mae.stm.offset / vo.type.size();
          auto ex1 = vo.ex1, ex2 = vo.ex2;
          auto t1 = ex1.valueType(), t2 = ex2.valueType();
          while (pretransform(ex1, t1) || pretransform(ex2, t2)) { }
          auto t1v = fastcast!(Vector) (t1), t2v = fastcast!(Vector) (t2);
          // logln("id is "[], id, " because of "[], mae.stm.offset, " into "[], vo.type.size(), "; compare "[], vo.valueType().size(), " / "[], (cast(Vector) vo.valueType()).real_len());
          // if (t1v) ex1 = getTupleEntries(reinterpret_cast(t1v.asFilledTup, ex1))[id];
          if (t1v) ex1 = mkTupleIndexAccess(reinterpret_cast(t1v.asFilledTup, ex1), id);
          if (t2v) {
            // logln("filled tup for "[], t2v, " is "[], t2v.asFilledTup, " -- "[], ex);
            // auto ar = getTupleEntries(reinterpret_cast(t2v.asFilledTup, ex2));
            // if (ar.length !> id) ex2 = fastalloc!(FailExpr)("oh fuck"[], ar[0].valueType());
            // else ex2 = ar[id];
            ex2 = mkTupleIndexAccess(reinterpret_cast(t2v.asFilledTup, ex2), id);
          }
          return fastcast!(Itr) (lookupOp(vo.op, ex1, ex2));
        }
      }
    }
    return null;
  };*/
}

Object gotMagnitude(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr >tree.expr.magnitude"[], &ex))
    return null;
  if (!t2.accept("|"[]))
    t2.failparse("Expected closing '|' for magnitude after "[], ex);
  auto ty = resolveType(ex.valueType());
  if (auto v = fastcast!(Vector) (ty)) {
    text = t2;
    Statement init1, init2;
    Expr tmp = lvize(ex, &init1);
    tmp = lookupOp("*"[], tmp, tmp);
    tmp = lvize(tmp, &init2);
    auto strct = v.asStruct;
    tmp = fastcast!(Expr) (strct.lookupRel("sqrt_sum"[], reinterpret_cast(strct, tmp)));
    if (init2) tmp = fastalloc!(StatementAndExpr)(init2, tmp);
    if (init1) tmp = fastalloc!(StatementAndExpr)(init1, tmp);
    return fastcast!(Object) (tmp);
  }
  if (Single!(Float) == ty) {
    text = t2;
    return fastcast!(Object)(iparse!(Expr, "abs_magn", "tree.expr")(`C_fabsf f`, "f", ex));
  }
  t2.failparse("Invalid type for magnitude: "[], ty);
}
mixin DefaultParser!(gotMagnitude, "tree.expr.magnitude"[], "24064"[], "|"[]);
