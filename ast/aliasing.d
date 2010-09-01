module ast.aliasing;

import ast.base, ast.parse, ast.structure, ast.namespace,
  tools.base: This, This_fn, rmSpace;

class ExprAlias : RelTransformable, Named, Expr {
  Expr base;
  string name;
  mixin This!("base, name");
  override {
    string getIdentifier() { return name; }
    Object transform(Expr relbase) {
      void delegate(ref Iterable) dg;
      dg = (ref Iterable iter) {
        if (auto rt = cast(RelTransformable) iter)
          iter = cast(Iterable) rt.transform(relbase);
        iter.iterate(dg);
      };
      auto it = cast(Iterable) base;
      dg(it);
      it.iterate(dg);
      return cast(Object) it;
    }
    void emitAsm(AsmFile af) {
      base.emitAsm(af); // may work .. or not.
    }
    IType valueType() { return base.valueType(); }
    mixin defaultIterate!(base);
    string toString() {
      return Format("expr-alias ", name, " = ", base);
    }
  }
}

class TypeAlias : Named, IType, TypeProxy {
  IType base;
  string name;
  mixin This!("base, name");
  override {
    string getIdentifier() { return name; }
    int size() { return base.size; }
    string mangle() { return base.mangle; }
    ubyte[] initval() { return base.initval; }
    int opEquals(IType ty) { return base.opEquals(ty); }
    IType actualType() { return base; }
    string toString() {
      return Format("type-alias ", name, " = ", base);
    }
  }
}

static import ast.fold;
static this() {
  ast.fold.opts ~= delegate Expr(Expr ex) {
    if (auto ea = cast(ExprAlias) ex) {
      return ea.base;
    } else return null;
  };
}

import ast.modules;
Object gotAlias(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("alias ")) {
    Expr ex;
    IType ty;
    string id;
    
    if (!(t2.gotIdentifier(id) &&
          t2.accept("=")))
      throw new Exception("Couldn't parse alias at "~t2.next_text());
    auto t3 = t2;
    if (rest(t3, "tree.expr", &ex) && t3.accept(";")) {
      t2 = t3;
    } else {
      t3 = t2;
      ex = null;
      if (rest(t3, "type", &ty) && t3.accept(";")) {
        t2 = t3;
      } else {
        throw new Exception("Couldn't parse alias target at "~t2.next_text());
      }
    }
    
    text = t2;
    if (ex) return new ExprAlias(ex, id);
    if (ty) return new TypeAlias(ty, id);
    assert(false);
  } else return null;
}
mixin DefaultParser!(gotAlias, "struct_member.struct_alias");
mixin DefaultParser!(gotAlias, "tree.toplevel.alias");