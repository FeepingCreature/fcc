module ast.vardecl_parse;

import parseBase, ast.base, ast.vardecl, ast.aliasing, ast.namespace, ast.expr_statement, ast.arrays,
       ast.casting, ast.pointer, ast.aggregate, ast.scopes, ast.types, ast.dg, tools.compat: find;

Scope cached_sc;
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, varname;
  bool isRefDecl, isScopeDecl;
  
  Scope sc;
  if (cached_sc) { sc = cached_sc; sc = sc._ctor(); cached_sc = null; }
  else { sc = new Scope; }
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  resetError();
  IType vartype;
  
  const abort = `cached_sc = sc; return null; `;
  
  if (!t2.accept("auto"[])) {
    if (t2.accept("ref"[])) isRefDecl = true;
    else if (t2.accept("scope"[])) isScopeDecl = true;
    
    if (!rest(t2, "type", &vartype) && !isScopeDecl && !isRefDecl) mixin(abort);
    if (t2.accept(":"[])) mixin(abort); // cast
  }
  
  if (t2.accept("("[])) mixin(abort); // compound var expr
  
  while (true) {
    if (!t2.gotIdentifier(varname, true))
      t2.failparse("Could not get variable identifier"[]);
    if (t2.acceptLeftArrow()) mixin(abort); // is an iterator-construct
    Expr ex;
    bool dontInit;
    if (t2.accept("="[])) {
      if (!rest(t2, "tree.expr"[], &ex)) {
        if (t2.accept("void")) {
          if (!vartype) t2.failparse("Cannot void-init typeless variable");
          dontInit = true;
        }
        else t2.failparse("Could not get variable initializer");
      }
      IType[] tried;
      if (vartype && !dontInit && !gotImplicitCast(ex, vartype, (IType it) { tried ~= it; return test(vartype == it); })) {
        t2.failparse("Couldn't init var: none of ", tried, " matched ", vartype);
      }
        
      if (isRefDecl) {
        auto lv = fastcast!(LValue) (ex);
        if (!lv)
          t2.failparse("Initializer of a ref decl must be referentiable");
        ex = fastalloc!(RefExpr)(lv);
      }
    } else if (isRefDecl) {
      t2.failparse("ref declaration must have initializer");
    } else if (!vartype) {
      t2.failparse("auto declaration must have initializer");
    }
    
    auto var = new Variable;
    if (!isRefDecl)
      var.name = varname;
    if (ex) {
      var.initval = ex;
      var.type = ex.valueType();
    } else {
      if (!vartype) fail; // shouldn't happen
      var.type = vartype;
      if (dontInit) var.dontInit = true;
      else var.initInit;
    }
    if (!var.type) fail; // shouldn't happen
    if (Single!(Void) == var.type) {
      t2.failparse("Cannot declare variable of type void");
    }
    if (isScopeDecl) {
      genRetvalHolder(sc); // do this before we grab the var position
    }
    var.baseOffset = boffs(var.type);
    auto vd = fastalloc!(VarDecl)(var);
    vd.configPosition(text);
    sc.addStatement(vd);
    sc.add(var); // was namespace()
    if (isRefDecl) {
      auto ea = fastalloc!(LValueAlias)(fastalloc!(DerefExpr)(var), varname);
      sc.add(ea);
    }
    if (isScopeDecl) {
      auto vt = resolveType(var.valueType());
      if (fastcast!(Array) (vt) || fastcast!(ExtArray) (vt) || showsAnySignOfHaving(var, "free")) {
        sc.addGuard(iparse!(Statement, "scope_guard", "tree.stmt")
                          (`var.free;`, "var", var));
      } else if (fastcast!(Delegate) (vt)) {
        sc.addGuard(iparse!(Statement, "scope_guard", "tree.stmt")
                          (`dupvfree var.data;`, "var", var));
      } else {
        sc.addGuard(iparse!(Statement, "scope_guard", "tree.stmt")
                          (`mem.free var;`, "var", var));
      }
    }
    if (t2.acceptTerminatorSoft()) break;
    if (t2.accept(","[])) continue;
    t2.failparse("Unexpected text in auto expr"[]);
  }
  text = t2;
  
  if (sc.guards.length) {
    auto supsc = fastcast!(Scope) (sc.sup);
    supsc.guards ~= sc.guards;
    supsc.guard_offsets ~= sc.guard_offsets;
  }
  foreach (entry; sc.field) {
    if (auto sa = fastcast!(SelfAdding) (entry._1)) if (sa.addsSelf()) continue;
    sc.sup.add(entry._0, entry._1);
  }
  
  return fastcast!(Object) (sc._body);
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl"[], "21"[]);
