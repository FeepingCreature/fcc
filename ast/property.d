module ast.property;

import ast.base, ast.fun, ast.funcall, ast.tuples, ast.variable, ast.vardecl, ast.namespace;

class Property : MValue, RelTransformable {
  Function getter, setter;
  PlaceholderToken ph;
  this(Function g, Function s, PlaceholderToken ph = null) {
    getter = g;
    setter = s;
    this.ph = ph;
    if (s.type.params.length != 1)
      fail;
    if (s.type.params[0].type != g.type.ret) {
      logln("setter: ", s.type.params[0].type);
      logln("getter: ", g.type.ret);
      fail;
    }
    if (s.type.ret != Single!(Void)) {
      fail;
    }
  }
  mixin defaultIterate!(getter, setter);
  override {
    Property dup() { return new Property(getter.dup, setter.dup, ph); }
    IType valueType() { return getter.type.ret; }
    void emitAsm(AsmFile af) {
      (buildFunCall(getter, mkTupleExpr(), "property-call")).emitAsm(af);
    }
    Object transform(Expr ex) {
      if (!ph) fail;
      Function g2 = getter, s2 = setter;
      void replace(ref Iterable it) {
        if (it is ph) it = ex;
        else it.iterate(&replace);
      }
      g2 = g2.dup;
      g2.iterateExpressions(&replace);
      s2 = s2.dup;
      s2.iterateExpressions(&replace);
      return new Property(g2, s2);
    }
    void emitAssignment(AsmFile af) {
      auto type = setter.type.params[0].type;
      auto var = new OffsetExpr(-af.currentStackDepth, type);
      (buildFunCall(setter, var, "property-write-call")).emitAsm(af);
      af.sfree(type.size);
    }
  }
}

Object gotPropertyExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  t2.mustAccept("(", "opening paren expected");
  string gid, sid;
  if (!t2.gotIdentifier(gid)) t2.failparse("Function name expected. ");
  t2.mustAccept(",", "comma expected");
  if (!t2.gotIdentifier(sid)) t2.failparse("Function name expected. ");
  t2.mustAccept(")", "closing paren expected");
  Function g, s;
  PlaceholderToken ph;
  if (auto rn = fastcast!(RelNamespace) (namespace())) {
    auto hrt = fastcast!(hasRefType) (rn);
    if (!hrt) { logln(rn); fail; }
    auto rt = hrt.getRefType();
    ph = new PlaceholderToken(rt, "interface placeholder");
    auto go = rn.lookupRel(gid, ph), so = rn.lookupRel(sid, ph);
    if (!go) text.failparse(gid, " not found");
    if (!so) text.failparse(gid, " not found");
    g = fastcast!(Function) (go); s = fastcast!(Function) (so);
  } else {
    auto go = namespace().lookup(gid), so = namespace().lookup(sid);
    if (!go) text.failparse(gid, " not found");
    if (!so) text.failparse(gid, " not found");
    g = fastcast!(Function) (go); s = fastcast!(Function) (so);
  }
  if (!g) text.failparse(gid, " is not a function");
  if (!s) text.failparse(sid, " is not a function");
  text = t2;
  return new Property(g, s, ph);
}
mixin DefaultParser!(gotPropertyExpr, "tree.expr.property_expr", "56", "accessor_property");
