// property-style function calls, ie. a.b(c) -> b(a, c)
module ast.propcall;

import
  ast.base, ast.mode, ast.namespace, ast.fun, ast.parse,
  ast.pointer, ast.nestfun;

class FirstParamOverrideSpace : Namespace, ScopeLike {
  Expr firstParam;
  this(Expr firstParam) { this.firstParam = firstParam; sup = namespace(); }
  override {
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() { return sup.stackframe(); }
    int framesize() { return (cast(ScopeLike) sup).framesize(); }
    Object lookup(string name, bool local = false) {
      auto res = sup.lookup(name, local);
      if (auto fun = cast(Function) res) {
        if (cast(NestedFunction) fun) goto fail;
        // logln("=> ", (cast(Object)fun).classinfo.name, " for ", fun);
        return new PrefixFunction(firstParam, fun);
      }
      fail:
      return null;
    }
  }
}

Object gotPropAccessExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(new FirstParamOverrideSpace(ex));
    
    Object res;
    auto t2 = text;
    // lol
    
    resetError;
    if (!rest(t2, "tree.expr _tree.expr.arith >tree.expr.properties", &res)) {
      text.setError("Couldn't get prop-access expr");
      return null;
    }
    text = t2;
    // logln("got fpos (", ex, ")");
    return res;
  };
}
// marked x for expensive :p
mixin DefaultParser!(gotPropAccessExpr, "tree.rhs_partial.x_propaccess", null, ".");
