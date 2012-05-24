module ast.context;

import ast.base, ast.parse, ast.structure, ast.namespace, ast.modules, ast.pointer, ast.globvars;

class PassthroughWeakNoOp : NoOp, IsMangled {
  IsMangled[] targets;
  this(IsMangled[] targets...) { this.targets = targets.dup; }
  string mangleSelf() { return null; }
  void markWeak() { foreach (tar; targets) tar.markWeak(); }
}

import tools.log;
Object gotContext(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!t2.gotIdentifier(name)) return null;
  auto st = fastalloc!(Structure)(namespace().mangle(name~"_data_struct"[], null));
  st.sup = namespace();
  
  // Copypasted from ast.structure
  auto rtptbackup = RefToParentType();
  scope(exit) RefToParentType.set(rtptbackup);
  RefToParentType.set(fastalloc!(Pointer)(st));
  
  auto rtpmbackup = *RefToParentModify();
  scope(exit) *RefToParentModify.ptr() = rtpmbackup;
  *RefToParentModify.ptr() = delegate Expr(Expr baseref) {
    return fastalloc!(DerefExpr)(baseref);
  };
  // end copypaste
  
  if (!t2.accept("{"[])) t2.failparse("expected opening context bracket"[]);
  if (matchStructBody(t2, st, &rest)) {
    if (!t2.accept("}"[]))
      t2.failparse("expected closing context bracket"[]);
  } else {
    t2.failparse("Couldn't match context body"[]);
  }
  
  auto gvd = new GlobVarDecl;
  gvd.tls = true;
  auto ctxvar = fastalloc!(GlobVar)(st, name, namespace(), true, cast(Expr) null);
  gvd.vars ~= ctxvar;
  namespace().add(ctxvar);
  
  IsMangled[] mangles;
  foreach (entry; st.field) if (auto m = fastcast!(IsMangled) (entry._1)) mangles ~= m;
  
  text = t2;
  fastcast!(Module) (current_module()).entries ~= gvd;
  return fastalloc!(PassthroughWeakNoOp)(mangles);
}
mixin DefaultParser!(gotContext, "tree.toplevel.context"[], null, "context"[]);
