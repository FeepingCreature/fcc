// property-style function calls, ie. a.b(c) -> b(a, c)
module ast.propcall;

import
  ast.base, ast.mode, ast.namespace, ast.fun, ast.parse,
  ast.pointer, ast.nestfun, ast.casting, ast.aliasing, ast.pointer;

bool incompat(IType a, IType b) {
  auto p1 = fastcast!(Pointer)~ a, p2 = fastcast!(Pointer)~ b;
  if (p1 && !p2 || p2 && !p1) return true;
  if (p1 && p2) return incompat(p1.target, p2.target);
  
  auto t1 = cast(TypeAlias) a, t2 = cast(TypeAlias) b;
  if (t1 && t2 && t1.name != t2.name) return true;
  
  return false;
}


// man this is such a hack.
class FirstParamOverrideSpace : Namespace, RelNamespace, IType {
  Expr firstParam;
  IType fpvt;
  this(Expr firstParam) { this.firstParam = firstParam; sup = namespace(); fpvt = firstParam.valueType(); }
  override {
    string toString() { return Format("fpos(", firstParam, ")"); }
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() { return sup.stackframe(); }
    Object lookup(string name, bool local = false) {
      auto res = sup.lookup(name, false);
      if (auto fun = fastcast!(Function) (res)) {
        if (fastcast!(NestedFunction)~ fun) return null;
        auto params = fun.getParams();
        if (!params.length) return null;
        auto pt = params[0].type;
        auto ex = firstParam;
        if (incompat(ex.valueType(), pt)) {
          // logln("Incompatible types: ", ex.valueType(), " and ", pt);
          // asm { int 3; }
          return null;
        }
        auto ex2 = ex;
        if (!gotImplicitCast(ex2, (IType it) { return test(it == pt); })) {
          // logln("no cast from ", ex, " to ", pt);
          return null;
        }
        return new PrefixFunction(ex2, fun);
      }
      return null;
    }
    Object lookupRel(string name, Expr base) {
      return lookup(name, false);
    }
    bool isTempNamespace() { return true; }
    int size() { return fpvt.size(); }
    string mangle() { assert(false); }
    ubyte[] initval() { return fpvt.initval(); }
    int opEquals(IType it) { return it is this; }
  }
}

// haaack.
class MyPlaceholderExpr : Expr {
  FirstParamOverrideSpace fpos;
  this(typeof(fpos) fpos) { this.fpos = fpos; }
  override {
    string toString() { return Format("propcall form for ", fpos.firstParam); }
    void iterate(void delegate(ref Iterable) dg) {
      Iterable forble = fpos.firstParam, forble2 = forble;
      dg(forble);
      if (forble !is forble2) {
        fpos.firstParam = fastcast!(Expr)~ forble;
        fpos.fpvt = fpos.firstParam.valueType();
      }
    }
    void emitAsm(AsmFile af) { fpos.firstParam.emitAsm(af); }
    MyPlaceholderExpr dup() { assert(false); }
    IType valueType() { return fpos; }
  }
}

// SUCH a hack. (do this last, save some time)
void setupPropCall() {
  implicits ~= delegate Expr(Expr ex) {
    if (cast(MyPlaceholderExpr) ex) return null;
    return new MyPlaceholderExpr(new FirstParamOverrideSpace(ex));
  };
}
