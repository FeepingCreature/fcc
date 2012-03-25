module ast.property;

import ast.base, ast.fun, ast.funcall, ast.tuples, ast.variable, ast.vardecl, ast.namespace, ast.pointer, ast.casting, ast.oop;

class Property : MValue, RelTransformable {
  Function getter, setter;
  PlaceholderToken ph;
  this(Function g, Function s, PlaceholderToken ph = null) {
    getter = g;
    setter = s;
    this.ph = ph;
    if (s.type.params.length != 1)
      fail;
    IType gettype;
    if (Single!(Void) == g.type.ret) {
      if (g.type.params.length != 1) throw new Exception("void getter must take single pointer argument");
      auto ptr = fastcast!(Pointer) (g.type.params[0].type);
      if (!ptr) throw new Exception("void getter must take single pointer argument");
      gettype = ptr.target;
    } else {
      gettype = g.type.ret;
    }
    if (s.type.params[0].type != gettype) {
      logln("setter: ", s.type.params[0].type);
      logln("getter: ", gettype);
      logln("setter and getter types are not compatible");
      fail;
    }
    if (s.type.ret != Single!(Void)) {
      fail;
    }
  }
  mixin defaultIterate!(getter, setter);
  override {
    Property dup() { return new Property(getter.dup, setter.dup, ph); }
    IType valueType() {
      if (Single!(Void) == getter.type.ret) {
        return fastcast!(Pointer) (getter.type.params[0].type).target;
      } else {
        return getter.type.ret;
      }
    }
    void emitAsm(AsmFile af) {
      mixin(mustOffset("valueType().size"));
      if (Single!(Void) == getter.type.ret) {
        mkVar(af, fastcast!(Pointer) (getter.type.params[0].type).target, false, (Variable var) {
          // logln("::", buildFunCall(getter, mkTupleExpr(new RefExpr(var)), "property-get-pointer-call"));
          // logln(fastcast!(Object) (buildFunCall(getter, mkTupleExpr(new RefExpr(var)), "property-get-pointer-call")).classinfo.name);
          (buildFunCall(getter, mkTupleExpr(new RefExpr(var)), "property-get-pointer-call")).emitAsm(af);
        });
      } else {
        (buildFunCall(getter, mkTupleExpr(), "property-call")).emitAsm(af);
      }
    }
    Object transform(Expr ex) {
      if (!ph) fail;
      Function g2 = getter, s2 = setter;
      if (!fastcast!(IntfRef) (ex.valueType())) {
        // struct or struct-like (class body)
        ex = reinterpret_cast(ph.type, new RefExpr(fastcast!(CValue) (ex))); // we're a data member, so we get the dereferenced version, but we need the reference version!
      }
      if (ph.type != ex.valueType()) {
        logln("Weird: ", ph.type, " vs. ", ex.valueType(), " - ", ph.type.size, " vs ", ex.valueType().size);
        fail;
      }
      void replace(ref Iterable it) {
        if (it is ph) it = ex;
        else it.iterate(&replace);
      }
      g2 = g2.dup;
      g2.iterate(&replace, IterMode.Semantic);
      s2 = s2.dup;
      s2.iterate(&replace, IterMode.Semantic);
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
  Object go, so;
  PlaceholderToken ph;
  if (auto rn = fastcast!(RelNamespace) (namespace())) {
    auto hrt = fastcast!(hasRefType) (rn);
    if (!hrt) { logln(rn); fail; }
    auto rt = hrt.getRefType();
    ph = new PlaceholderToken(rt, "interface placeholder");
    go = rn.lookupRel(gid, ph); so = rn.lookupRel(sid, ph);
    if (!go) text.failparse(gid, " not found");
    if (!so) text.failparse(gid, " not found");
    g = fastcast!(Function) (go); s = fastcast!(Function) (so);
  } else {
    go = namespace().lookup(gid); so = namespace().lookup(sid);
    if (!go) text.failparse(gid, " not found");
    if (!so) text.failparse(gid, " not found");
    g = fastcast!(Function) (go); s = fastcast!(Function) (so);
  }
  if (!g) text.failparse(gid, " is not a function: ", go);
  if (!s) text.failparse(sid, " is not a function: ", so);
  text = t2;
  return new Property(g, s, ph);
}
mixin DefaultParser!(gotPropertyExpr, "tree.expr.property_expr", "56", "accessor_property");
