// property-style function calls, ie. a.b(c) -> b(a, c)
module ast.propcall;

import
  ast.base, ast.mode, ast.namespace, ast.fun, ast.parse, ast.prefixfun,
  ast.pointer, ast.nestfun, ast.casting, ast.aliasing, ast.pointer;

bool incompat(IType a, IType b) {
  auto p1 = fastcast!(Pointer)~ a, p2 = fastcast!(Pointer)~ b;
  if (p1 && !p2 || p2 && !p1) return true;
  if (p1 && p2) return incompat(p1.target, p2.target);
  
  // MEH!!
  // auto t1 = cast(TypeAlias) a, t2 = cast(TypeAlias) b;
  // if (t1 && t2 && t1.name != t2.name) return true;
  
  return false;
}

// man this is such a hack.
import ast.templ; // this also!
class FirstParamOverrideSpace : Namespace, RelNamespace, IType, WithAware, ISafeSpaceTag {
  Expr firstParam;
  IType fpvt;
  bool implicit;
  this(Expr firstParam) { this.firstParam = firstParam; sup = namespace(); fpvt = firstParam.valueType(); }
  Object lookupInternal(string name, bool local = false, bool isDirectLookup = true) {
    auto res = sup.lookup(name, local);
    if (isDirectLookup) if (auto templ = fastcast!(Template) (res)) {
      return fastalloc!(PrefixTemplate)(firstParam, templ);
    }
    PrefixFunction processFun(Function fun) {
      auto params = fun.getParams();
      if (!params.length) return null;
      auto pt = params[0].type;
      if (incompat(fpvt, pt)) {
        // logln("Incompatible types: "[], fpvt, " and "[], pt);
        // fail;
        return null;
      }
      auto ex2 = firstParam;
      if (!gotImplicitCast(ex2, (IType it) { return test(it == pt); })) {
        // logln("no cast from "[], firstParam, " to "[], pt);
        return null;
      }
      return fastalloc!(PrefixFunction)(ex2, fun);
    }
    if (auto fun = fastcast!(Function) (res)) {
      if (auto res2 = processFun(fun)) {
        if (implicit) // comes from using() = not 100% sure if a match
          return fastcast!(Object) ((fastalloc!(OverloadSet)(fun.name)).extend(fun).extend(res2));
        else // comes from a.b = definitely a match
          return res2;
      }
    }
    if (auto os = fastcast!(OverloadSet) (res)) {
      Extensible resx = fastalloc!(OverloadSet)(os.name);
      foreach (fun; os.funs)
        resx = resx.extend(fun);
      foreach (fun; os.funs)
        if (auto res = processFun(fun)) {
          resx = resx.extend(res);
        }
      auto os2 = fastcast!(OverloadSet) (resx);
      if (!os2.funs.length) return null;
      if (os2.funs.length == 1) return os2.funs[0];
      return os2;
    }
    return null;
  }
  override {
    Object forWith() {
      auto res = fastalloc!(FirstParamOverrideSpace)(firstParam);
      res.sup = sup;
      res.implicit = true;
      return res;
    }
    string toString() { return Format("fpos of a "[], fpvt); }
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() { return sup.stackframe(); }
    bool isPointerLess() { return fpvt.isPointerLess(); }
    bool isComplete() { return fpvt.isComplete(); }
    Object lookup(string name, bool local = false) {
      return lookupInternal(name, local, true);
    }
    Object lookupRel(string name, Expr base, bool isDirectLookup = true) {
      return lookupInternal(name, false, isDirectLookup);
    }
    bool isTempNamespace() { return true; }
    int size() { return fpvt.size(); }
    string mangle() { return fpvt.mangle(); /* equivalent */ }
    ubyte[] initval() { return fpvt.initval(); }
    int opEquals(IType it) { return it is this; }
    IType proxyType() { return null; }
  }
}

// haaack.
class MyPlaceholderExpr : Expr {
  FirstParamOverrideSpace fpos;
  this(typeof(fpos) fpos) { this.fpos = fpos; }
  override {
    string toString() { return Format("propcall form for "[], fpos.firstParam); }
    void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
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
  implicits ~= delegate Expr(Expr ex, IType it) {
    if (fastcast!(MyPlaceholderExpr) (ex)) return null;
    if (it) return null; // we want a specific type - no sense in trying the overrides
    return fastalloc!(MyPlaceholderExpr)(fastalloc!(FirstParamOverrideSpace)(forcedConvert(ex)));
  };
}
