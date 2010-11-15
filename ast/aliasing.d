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

class CValueAlias : ExprAlias, CValue {
  mixin MyThis!("super(base, name)");
  override void emitLocation(AsmFile af) { (cast(CValue) base).emitLocation(af); }
  override CValueAlias dup() { return new CValueAlias(base.dup, name); }
}

class LValueAlias : CValueAlias, LValue {
  mixin MyThis!("super(base, name)");
  override LValueAlias dup() { return new LValueAlias(base.dup, name); }
}

class MValueAlias : ExprAlias, MValue {
  mixin MyThis!("super(base, name)");
  override void emitAssignment(AsmFile af) { (cast(MValue) base).emitAssignment(af); }
  override MValueAlias dup() { return new MValueAlias(base.dup, name); }
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
    string toString() { return Format(name, "(", base, ")"); }
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
    Object obj;
    string id;
    bool notDone;
    
redo:
    if (!(t2.gotIdentifier(id) &&
          t2.accept("=")))
      t2.failparse("Couldn't parse alias");
    auto t3 = t2;
    bool gotTerm() {
      if (t3.accept(";")) return true;
      if (t3.accept(",")) {
        notDone = true;
        return true;
      }
      return false;
    }
    if (rest(t3, "tree.expr", &ex) && gotTerm()) {
      t2 = t3;
    } else {
      t3 = t2;
      ex = null;
      if (rest(t3, "type", &ty) && gotTerm()) {
        t2 = t3;
      } else {
        t3 = t2;
        if (rest(t3, "tree.expr", &obj) && gotTerm()) {
          t2 = t3;
          namespace().__add(id, obj); // for instance, function alias
        } else
          t2.failparse("Couldn't parse alias target");
      }
    }
    
    assert(ex || ty || obj);
    text = t2;
    auto cv = cast(CValue) ex, mv = cast(MValue) ex, lv = cast(LValue) ex;
    if (ex) {
      ExprAlias res;
      if (lv) res = new LValueAlias(lv, id);
      else if (mv) res = new MValueAlias(mv, id);
      else if (cv) res = new CValueAlias(cv, id);
      else res = new ExprAlias(ex, id);
      namespace().add(res);
    }
    if (ty) namespace().add(new TypeAlias(ty, id));
    if (notDone) {
      notDone = false;
      goto redo;
    }
    return Single!(NamedNull);
  } else return null;
}
mixin DefaultParser!(gotAlias, "struct_member.struct_alias");
mixin DefaultParser!(gotAlias, "tree.stmt.alias", "16");
mixin DefaultParser!(gotAlias, "tree.toplevel.alias");
