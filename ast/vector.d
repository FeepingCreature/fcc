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
  bool extend() { return len == 3 && base == Single!(Float); }
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
  retryTup:
  auto tup = fastcast!(Tuple)~ ex.valueType();
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

Vector vec3f;

bool gotSSEVecOp(AsmFile af, LValue op1, LValue op2, LValue res, string op) {
  if (!vec3f) vec3f = new Vector(Single!(Float), 3);
  if (op != "+") return false;
  if (op1.valueType() != vec3f
   || op2.valueType() != vec3f)
    return false;
  op1.emitLocation(af);
  op2.emitLocation(af);
  res.emitLocation(af);
  af.popStack("%ecx", voidp);
  af.popStack("%eax", voidp);
  af.popStack("%ebx", voidp);
  af.SSEOp("movaps", "(%ebx)", "%xmm0");
  af.SSEOp("movaps", "(%eax)", "%xmm1");
  af.SSEOp("addps", "%xmm1", "%xmm0");
  af.SSEOp("movaps", "%xmm0", "(%ecx)");
  
  return true;
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
      while (true) {
        if (pretransform(ex1, t1)) continue;
        if (pretransform(ex2, t2)) continue;
        break;
      }
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
        if (!gotSSEVecOp(af, fastcast!(LValue) (v1), fastcast!(LValue) (v2), fastcast!(LValue) (var), op)) {
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

import ast.opers;
static this() {
  Expr handleVecOp(string op, Expr lhs, Expr rhs) {
    auto v1 = lhs.valueType(), v2 = rhs.valueType();
    while (true) {
      if (pretransform(lhs, v1)) continue;
      if (pretransform(rhs, v2)) continue;
      break;
    }
    auto v1v = fastcast!(Vector)~ v1, v2v = fastcast!(Vector)~ v2;
    if (!v1v && !v2v) return null;
    
    assert(!v1v || !v2v || v1v.asTup.types.length == v2v.asTup.types.length, Format("Mismatching tuple types: ", v1v, " and ", v2v));
    int len;
    if (v1v) len = v1v.asTup.types.length;
    else len = v2v.asTup.types.length;
    
    auto l1 = lhs; if (v1v) l1 = getTupleEntries(reinterpret_cast(v1v.asFilledTup, lhs))[0];
    auto r1 = rhs; if (v2v) r1 = getTupleEntries(reinterpret_cast(v2v.asFilledTup, rhs))[0];
    auto type = lookupOp(op, l1, r1).valueType();
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
  defineOp("-", &negate);
  defineOp("-", "-" /apply/ &handleVecOp);
  defineOp("+", "+" /apply/ &handleVecOp);
  defineOp("*", "*" /apply/ &handleVecOp);
  defineOp("/", "/" /apply/ &handleVecOp);
}
