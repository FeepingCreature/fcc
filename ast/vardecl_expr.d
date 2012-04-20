module ast.vardecl_expr;

import ast.scopes, ast.namespace, ast.casting, ast.base, ast.types, ast.parse, ast.vardecl, ast.tuples,
       ast.assign, ast.aggregate, ast.c_bind;

Object gotVarDeclExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  IType type;
  {
    string t3 = t2;
    if (t3.accept("("[]) && t3.accept(")"[])) /* THIS IS NOT A GOOD THING THIS IS BAD AND WRONG */
      return null; // whew.
  }
  if (parsingCHeader()) return null;
  if (!t2.accept("auto"[]))
    if (!rest(t2, "type"[], &type)) return null;
  if (t2.accept(":"[])) return null; // cast
  bool completeDeclaration(Statement* st, Expr* ex) {
    bool dontInit;
    Expr initval;
    if (t2.accept("="[])) {
      if (t2.accept("void"[])) { dontInit = true; }
      else {
        IType[] its;
        if (!rest(t2, "tree.expr"[], &initval)
          || type && !gotImplicitCast(initval, type, (IType it) {
          its ~= it;
          return test(type == it);
        }))
          t2.failparse("Could not parse variable initializer; tried "[], its);
        if (!type) type = initval.valueType();
      }
    } else {
      if (!type) {
        t2.setError("Auto vardecl exprs must be initialized. "[]);
        return false;
      }
      if (t2.acceptLeftArrow()) return false; // don't collide with iterator declaration
    }
    if (fastcast!(Void) (resolveType(type))) {
      text.failparse("Cannot declare variable of type "[], type, " which is void"[]);
    }
    auto var = fastalloc!(Variable)(type, name, boffs(type));
    auto sc = namespace().get!(Scope);
    if (!sc) {
      t2.failparse("There is a lack of a scope here; trying to define "[], name);
    }
    try sc.add(var);
    catch (AlreadyDefinedException ex) {
      t2.failparse(ex);
    }
    auto vd = fastalloc!(VarDecl)(var);
    vd.configPosition(text);
    sc.addStatement(vd);
    if (!initval) {
      var.initInit; *ex = var;
    } else {
      var.dontInit = true;
      if (!dontInit)
        *st = fastalloc!(Assignment)(var, initval);
      *ex = var;
    }
    return true;
  }
  Statement setVar;
  Expr res;
  if (t2.gotValidIdentifier(name)) {
    if (!completeDeclaration(&setVar, &res)) return null;
  } else if (t2.accept("("[])) {
    bool firstTime = true;
    bool wasAuto = !type;
    Statement[] stmts; Expr[] exprs;
    while (true) {
      if (t2.accept(")"[])) break;
      if (firstTime) firstTime = false;
      else {
        if (!t2.accept(","[])) t2.failparse("Comma expected"[]);
      }
      if (!t2.gotValidIdentifier(name)) t2.failparse("Identifier expected"[]);
      Statement st; Expr ex;
      if (!completeDeclaration(&st, &ex)) t2.failparse("Declaration completion expected"[]);
      exprs ~= ex;
      if (st) stmts ~= st;
      if (wasAuto) type = null;
    }
    if (stmts) setVar = fastalloc!(AggrStatement)(stmts);
    res = mkTupleExpr(exprs);
  } else return null;
  
  text = t2;
  if (setVar) return fastalloc!(StatementAndExpr)(setVar, res);
  else return fastcast!(Object) (res);
}
mixin DefaultParser!(gotVarDeclExpr, "tree.expr.vardecl"[], "28"[]);

