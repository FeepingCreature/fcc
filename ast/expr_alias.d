module ast.expr_alias;

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
      return Format("alias ", base, " ", name);
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
mixin DefaultParser!(gotExprAlias, "tree.toplevel.expr_alias");
