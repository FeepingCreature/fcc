module ast.context;

import ast.base, ast.parse, ast.structure, ast.namespace, ast.modules, ast.pointer, ast.globvars;

import tools.log;
Object gotContext(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!t2.gotIdentifier(name)) return null;
  auto st = new Structure(namespace().mangle(name~"_data_struct", null));
  st.sup = namespace();
  
  // Copypasted from ast.structure
  auto rtptbackup = RefToParentType();
  scope(exit) RefToParentType.set(rtptbackup);
  RefToParentType.set(new Pointer(st));
  
  auto rtpmbackup = *RefToParentModify();
  scope(exit) *RefToParentModify.ptr() = rtpmbackup;
  *RefToParentModify.ptr() = delegate Expr(Expr baseref) {
    return new DerefExpr(baseref);
  };
  // end copypaste
  
  if (!t2.accept("{")) t2.failparse("expected opening context bracket");
  if (matchStructBody(t2, st, &rest)) {
    if (!t2.accept("}"))
      t2.failparse("expected closing context bracket");
  } else {
    t2.failparse("Couldn't match context body");
  }
  
  auto gvd = new GlobVarDecl;
  gvd.tls = true;
  auto ctxvar = new GlobVar(st, name, namespace(), true, null);
  gvd.vars ~= ctxvar;
  namespace().add(ctxvar);
  
  text = t2;
  fastcast!(Module) (current_module()).entries ~= gvd;
  return Single!(NoOp);
}
mixin DefaultParser!(gotContext, "tree.toplevel.context", null, "context");
