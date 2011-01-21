// property-style function calls, ie. a.b(c) -> b(a, c)
module ast.propcall;

import
  ast.base, ast.mode, ast.namespace, ast.fun, ast.parse,
  ast.pointer, ast.nestfun, ast.casting;

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
      auto res = sup.lookup(name, local);
      if (auto fun = cast(Function) res) {
        if (cast(NestedFunction) fun) goto fail;
        auto pt = fun.getParams[0]._0;
        auto ex = firstParam;
        if (!gotImplicitCast(ex, (IType it) { return test(it == pt); }))
          return null;
        return new PrefixFunction(ex, fun);
      }
      fail:
      return null;
    }
    Object lookupRel(string name, Expr base) {
      return lookup(name, false);
    }
    bool isTempNamespace() { return true; }
    int size() { return fpvt.size(); }
    string mangle() { assert(false); }
    ubyte[] initval() { return fpvt.initval(); }
    int opEquals(IType it) { return false; }
  }
}

// haaack.
class MyPlaceholderExpr : Expr {
  FirstParamOverrideSpace fpos;
  this(typeof(fpos) fpos) { this.fpos = fpos; }
  override {
    void iterate(void delegate(ref Iterable) dg) {
      Iterable forble = fpos.firstParam, forble2 = forble;
      dg(forble);
      if (forble !is forble2) {
        fpos.firstParam = cast(Expr) forble;
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
