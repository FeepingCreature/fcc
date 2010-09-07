module ast.aliasing;

import ast.base, ast.parse, ast.structure, ast.namespace,
  tools.base: This, This_fn, rmSpace;

class ExprAlias : RelTransformable, Named, Expr, SelfAdding {
  Expr base;
  string name;
  mixin MyThis!("base, name");
  mixin DefaultDup!();
  mixin defaultIterate!(base);
  override {
    bool addsSelf() { return true; }
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
    string toString() {
      return Format("expr-alias ", name, " = ", base);
    }
  }
}

class TypeAlias : Named, IType, TypeProxy, SelfAdding {
  IType base;
  string name;
  mixin This!("base, name");
  override {
    bool addsSelf() { return true; }
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

static this() {
  foldopt ~= delegate Expr(Expr ex) {
    if (auto ea = cast(ExprAlias) ex) {
      return ea.base;
    } else return null;
  };
}

class NamedNull : NoOp, Named, SelfAdding {
  override string getIdentifier() { return null; }
  override bool addsSelf() { return true; }
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
    
    assert(ex || ty);
    text = t2;
    if (ex) namespace().add(new ExprAlias(ex, id));
    if (ty) namespace().add(new TypeAlias(ty, id));
    return Single!(NamedNull);
  } else return null;
}
mixin DefaultParser!(gotAlias, "struct_member.struct_alias");
mixin DefaultParser!(gotAlias, "tree.stmt.alias");
mixin DefaultParser!(gotAlias, "tree.toplevel.alias");
