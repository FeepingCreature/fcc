module ast.vardecl_expr;

import ast.scopes, ast.namespace, ast.casting, ast.base, ast.types, ast.parse, ast.vardecl, ast.tuples,
       ast.assign, ast.aggregate, ast.c_bind, ast.pointer, ast.aliasing;

Object gotVarDeclExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  IType type;
  {
    string t3 = t2;
    if (t3.accept("("[]) && t3.accept(")"[])) /* THIS IS NOT A GOOD THING THIS IS BAD AND WRONG */
      return null; // whew.
  }
  if (parsingCHeader() || !namespace().get!(ScopeLike)) return null;
  bool isRefDecl;
  if (!t2.accept("auto"[])) {
    if (t2.accept("ref")) isRefDecl = true;
    if (!rest(t2, "type"[], &type) && !isRefDecl) return null;
  }
  if (t2.accept(":"[])) return null; // cast
  bool completeDeclaration(Statement* st, Expr* ex) {
    bool dontInit;
    Expr initval;
    if (t2.accept("="[])) {
      if (t2.accept("void"[])) {
        dontInit = true;
        if (!type) text.failparse("uninitialized variables must have type");
      } else {
        IType[] its;
        if (!rest(t2, "tree.expr"[], &initval)
          || type && !gotImplicitCast(initval, type, (IType it) {
          its ~= it;
          return test(type == it);
        }))
          t2.failparse("Could not parse variable initializer; tried "[], its);
      }
    } else {
      if (!type) {
        t2.setError("Auto vardecl exprs must be initialized. "[]);
        return false;
      }
      if (t2.acceptLeftArrow()) return false; // don't collide with iterator declaration
    }
    Variable var;
    if (isRefDecl) {
      if (!initval)
        text.failparse("ref declaration must have initializer");
      auto lv = fastcast!(LValue)(initval);
      if (!lv)
        text.failparse("initializer of a ref decl must be referentiable");
      initval = fastalloc!(RefExpr)(lv);
      if (type && type != initval.valueType())
        text.failparse("Type mismatch: declared ", type, " but got ", initval.valueType());
      type = initval.valueType();
      var = fastalloc!(Variable)(type, framelength(), cast(string) null);
    } else {
      if (!type) {
        if (!initval) text.failparse("internal compiler bug - no init no type");
        type = initval.valueType();
        if (!initval) text.failparse("internal compiler bug - no init no type even now");
      }
      var = fastalloc!(Variable)(type, framelength(), name);
    }
    if (fastcast!(Void) (resolveType(type))) {
      text.failparse("Cannot declare variable of type "[], type, " which is void"[]);
    }
    auto sc = namespace().get!(Scope);
    if (!sc) {
      t2.failparse("There is a lack of a scope here; trying to define "[], name);
    }
    try {
      sc.add(var);
    } catch (AlreadyDefinedException ex) {
      t2.failparse(ex);
    }
    if (isRefDecl) {
      auto ea = fastalloc!(LValueAlias)(fastalloc!(DerefExpr)(var), name);
      sc.add(ea);
      *ex = ea;
    } else {
      *ex = var;
    }
    auto vd = fastalloc!(VarDecl)(var);
    vd.configPosition(text);
    sc.addStatement(vd);
    if (initval) {
      if (!dontInit)
        *st = fastalloc!(Assignment)(var, initval);
    } else {
      vd.initInit;
    }
    return true;
  }
  Statement setVar;
  Expr res;
  if (t2.gotIdentifier(name)) {
    if (!completeDeclaration(&setVar, &res)) return null;
  } else if (t2.accept("("[])) {
    bool firstTime = true;
    bool wasAuto = !type;
    Statement[] stmts; Expr[] exprs;
    while (true) {
      if (t2.accept(")"[])) break;
      if (firstTime) firstTime = false;
      else {
        if (!t2.accept(","[])) { t2.setError("Comma expected"[]); return null; }
      }
      if (!t2.gotIdentifier(name)) t2.failparse("Identifier expected"[]);
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
mixin DefaultParser!(gotVarDeclExpr, "tree.expr.vardecl", "28", null, true, true);

