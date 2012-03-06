module ast.condprop; // conditional property

import
  parseBase, ast.base, ast.properties, ast.parse, ast.modules,
  ast.casting, ast.vardecl, ast.properties_parse, ast.static_arrays,
  ast.namespace, ast.scopes, ast.ifstmt, ast.assign;

Object gotCondProperty(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto nullthing = fastcast!(Expr) (sysmod.lookup("null"));
    auto evt = ex.valueType();
    
    auto testthing = nullthing;
    if (!gotImplicitCast(testthing, evt, (IType it) { return test(it == evt); }))
      return null;
    
    return fastcast!(Object) (tmpize(ex, delegate Expr(Expr base, OffsetExpr oe) {
      auto proprest_obj = getProperties(t2, fastcast!(Object) (base), true, true, cont, rest);
      auto proprest = fastcast!(Expr) (proprest_obj);
      if (!proprest_obj || !proprest)
        t2.failparse("couldn't get continuing property for ", base, " - ", proprest_obj);
      Expr elsecase;
      if (t2.accept(":")) {
        if (!rest(t2, "tree.expr _tree.expr.arith", &elsecase))
          t2.failparse("Else property expected");
      }
      auto prvt = proprest.valueType();
      if (elsecase && elsecase.valueType() != prvt) {
        t2.failparse("Mismatched types: ", prvt, " and ", elsecase.valueType());
      }
      
      oe.type = prvt;
      
      bool isVoid = test(Single!(Void) == prvt);
      
      auto ifs = new IfStatement;
      ifs.wrapper = new Scope;
      ifs.wrapper.requiredDepthDebug ~= " (ast.condprop:31)";
      ifs.wrapper.pad_framesize = base.valueType().size + isVoid?0:oe.type.size;
      ifs.wrapper.requiredDepth += ifs.wrapper.pad_framesize;
      // namespace.set(ifs.wrapper);
      // scope(exit) namespace.set(ifs.wrapper.sup);
      ifs.test = iparse!(Cond, "cp_cond", "cond")
                        (`base`, "base", base);
      configure(ifs.test);
      
      Expr res;
      if (isVoid) {
        ifs.branch1 = new ExprStatement(proprest);
        if (elsecase) ifs.branch2 = new ExprStatement(elsecase);
        res = mkStatementAndExpr(ifs, Single!(VoidExpr));
      } else {
        ifs.branch1 = new Assignment(oe, proprest);
        auto ovt = oe.valueType();
        if (!elsecase) elsecase = reinterpret_cast(ovt, new DataExpr(ovt.initval()));
        ifs.branch2 = new Assignment(oe, elsecase);
        res = mkStatementAndExpr(ifs, oe);
      }
      ifs.wrapper.requiredDepth = int.max; // force tolerance
      text = t2;
      return res;
    }));
  };
}
mixin DefaultParser!(gotCondProperty, "tree.rhs_partial.condprop", null, "?");
