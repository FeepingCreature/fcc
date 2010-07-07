module ast.expr_alias;

import ast.base, ast.parse, ast.structure, ast.namespace,
  tools.base: This, This_fn, rmSpace;

class ExprAlias : Expr, RelTransformable, Named {
  Expr base;
  string name;
  mixin This!("base, name");
  mixin defaultIterate!(base);
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
      logln("transform ", name, " with ", base, ": ", it);
      return cast(Object) it;
    }
    string toString() {
      return Format("alias ", base, " ", name);
    }
    IType valueType() { return base.valueType(); }
    import tools.base;
    void emitAsm(AsmFile af) { assert(false); }
  }
}

import ast.modules;
Object gotExprAlias(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("alias ")) {
    Expr ex;
    string id;
    
    if (!(t2.gotIdentifier(id) &&
          t2.accept("=") &&
          rest(t2, "tree.expr", &ex) &&
          t2.accept(";"))) {
      throw new Exception("Couldn't parse expr alias at "~t2.next_text());
    }
    
    text = t2;
    return new ExprAlias(ex, id);
  } else return null;
}
mixin DefaultParser!(gotExprAlias, "struct_member.struct_expr_alias");
