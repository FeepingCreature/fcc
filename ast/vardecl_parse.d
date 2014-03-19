module ast.vardecl_parse;

import parseBase, ast.base, ast.vardecl, ast.aliasing, ast.namespace, ast.expr_statement,
       ast.types, ast.dg, ast.pointer, ast.arrays, ast.tuples, ast.tuple_access,
       ast.casting, ast.aggregate, ast.scopes, tools.compat: find;

Scope cached_sc;
// TODO unify with vardecl_expr
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, varname;
  bool isRefDecl, isScopeDecl;
  
  Scope sc;
  if (cached_sc) { sc = cached_sc; sc = sc._ctor(); cached_sc = null; }
  else { sc = fastalloc!(Scope)(); }
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
    bool exportNamedTupleMembers;
    if (!t2.gotIdentifier(varname, true)) {
      auto t3 = t2;
      if ((vartype || isRefDecl || isScopeDecl) && t3.accept("="))
      { /* nameless variable */
        // logln("nameless? but ", vartype, ", ", isRefDecl, ", ", isScopeDecl, " at ", t2.nextText());
        // nameless tuple decls are "transparent"
        // (int a, int) = (2, 3); a = 4;
        // this is mainly to make up for the ambiguity with (int a, int b) = (2, 3);
        // which becomes an anonymous named tuple decl instead of a tuple of variable decls
        // (the two cases should be functionally indistinguishable)
        exportNamedTupleMembers = true;
        varname = getAnonvarId();
      } else {
        if (vartype && fastcast!(Tuple) (vartype)) { // might be a (vardecl) form tuple!
          t2.setError("Could not get variable identifier");
          return null;
        }
        t2.failparse("Could not get variable identifier"[]);
      }
    }
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
      if (vartype && !dontInit && !gotImplicitCast(ex, vartype, (IType it) { tried ~= it; return test(vartype == it); }, false)) {
        t2.failparse("Couldn't init var: none of ", tried, " matched ", vartype);
      }
      
      if (isRefDecl) {
        auto lv = fastcast!(LValue) (ex);
        if (!lv)
          t2.failparse("Initializer of a ref decl must be referentiable");
        ex = fastalloc!(RefExpr)(lv);
        if (vartype) vartype = fastalloc!(Pointer)(vartype);
      }
    } else if (isRefDecl) {
      t2.failparse("ref declaration must have initializer");
    } else if (!vartype) {
      t2.failparse("auto declaration must have initializer");
    }
    
    auto var = fastalloc!(Variable)();
    VarDecl vd;
    if (!isRefDecl)
      var.name = varname;
    if (ex) {
      if (vartype) var.type = vartype;
      else var.type = ex.valueType();
      vd = fastalloc!(VarDecl)(var, ex);
    } else {
      if (!vartype) fail; // shouldn't happen
      var.type = vartype;
      vd = fastalloc!(VarDecl)(var);
      if (!dontInit) vd.initInit;
    }
    if (!var.type) fail; // shouldn't happen
    var.stacktype = frametypePlus(var.type);
    
    if (Single!(Void) == var.type) {
      t2.failparse("Cannot declare variable of type void");
    }
    var.baseIndex = framelength();
    vd.configPosition(text);
    sc.addStatement(vd);
    sc.add(var); // was namespace()
    if (isRefDecl) {
      auto ea = fastalloc!(LValueAlias)(fastalloc!(DerefExpr)(var), varname);
      sc.add(ea);
    }
    if (isScopeDecl) {
      sc.addGuard(freeVar(var));
    }
    if (exportNamedTupleMembers) {
      if (auto tup = fastcast!(Tuple)(var.valueType())) {
        auto members = getTupleEntries(var);
        foreach (i, name; tup.names) if (name) {
          sc.add(fastalloc!(LValueAlias)(members[i], name));
        }
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
