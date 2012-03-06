module ast.vardecl_parse;

import parseBase, ast.base, ast.vardecl, ast.aliasing, ast.namespace,
       ast.casting, ast.pointer, ast.aggregate, ast.scopes, ast.types, tools.compat: find;
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = new Scope;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  string name; IType type;
  bool abortGracefully;
  if (rest(t2, "type", &type)) {
    if (t2.accept(":")) return null; // cast
    if (t2.accept("(")) return null; // compound var expr
    if (!t2.bjoin(t2.gotValidIdentifier(name), t2.accept(","), {
      auto var = new Variable;
      var.name = name;
      var.type = type;
      bool dontInit;
      if (t2.accept("<-")) { abortGracefully = true; return; } // aaaa
      if (t2.accept("=")) {
        IType[] its;
        auto t3 = t2;
        if ((!rest(t2, "tree.expr", &var.initval) || !gotImplicitCast(var.initval, var.type, (IType it) {
          its ~= it;
          return test(var.type == it);
        })) && (t2 = t3, true) && !(t2.accept("void") && (dontInit = true, true))) {
          if (its.length) t2.failparse("Couldn't init var; none of ", its, " matched ", var.type);
          else t2.failparse("Couldn't read expression");
        }
      }
      if (dontInit) {
        var.dontInit = true;
      } else {
        var.initInit();
        if (var.type != Single!(Void)) {
          assert(!!var.initval);
          if (var.type != var.initval.valueType())
            throw new Exception(Format("Mismatching types in initializer: ", var, " of ", var.type, " <- ", var.initval.valueType()));
        }
      }
      var.baseOffset = boffs(var.type);
      auto vd = new VarDecl(var);
      vd.configPosition(text);
      sc.addStatement(vd);
      try sc.add(var); // was: namespace()
      catch (AlreadyDefinedException ade) {
        text.failparse(ade);
      }
    }, false)) {
      if (abortGracefully) return null;
      t2.failparse("Couldn't parse variable declaration");
    }
    if (abortGracefully) return null;
    t2.mustAcceptTerminatorSoft("Missed trailing semicolon");
    text = t2;
    if (sc.guards.length) fail;
    // collapse
    foreach (entry; sc.field) {
      if (auto sa = fastcast!(SelfAdding) (entry._1)) if (sa.addsSelf()) continue;
      sc.sup.add(entry._0, entry._1);
    }
    return fastcast!(Object) (sc._body);
  } else return null;
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl", "21");

Object gotAutoDecl(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, varname;
  Expr ex;
  bool isRefDecl;
  
  auto sc = new Scope;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  string t3;
  resetError();
  if (!t2.accept("auto")) {
    if (!t2.accept("ref")) return null;
    isRefDecl = true;
  }
  if (t2.accept("(")) return null; // compound var expr
  while (true) {
    if (!t2.gotValidIdentifier(varname, true))
      t2.failparse("Could not get variable identifier");
    if (t2.accept("<-")) return null; // is an iterator-construct
    if (!t2.accept("="))
      t2.failparse("Could not get auto initializer");
    if (!rest(t2, "tree.expr", &ex))
      t2.failparse("Could not get auto init expression");
    auto lv = fastcast!(LValue) (ex);
    if (isRefDecl) {
      if (!lv)
        t2.failparse("Initializer of a ref decl must be referentiable");
      ex = new RefExpr(lv);
    }
    
    auto var = new Variable;
    if (!isRefDecl)
      var.name = varname;
    var.initval = ex;
    var.type = ex.valueType();
    if (!var.type) {
      t2.failparse("Expression has no type (wtf?) ", ex);
    }
    var.baseOffset = boffs(var.type);
    auto vd = new VarDecl(var);
    vd.configPosition(text);
    sc.addStatement(vd);
    sc.add(var); // was namespace()
    if (isRefDecl) {
      auto ea = new LValueAlias(new DerefExpr(var), varname);
      sc.add(ea);
    }
    if (t2.acceptTerminatorSoft()) break;
    if (t2.accept(",")) continue;
    t2.failparse("Unexpected text in auto expr");
  }
  text = t2;
  if (sc.guards.length) fail;
  // collapse
  foreach (entry; sc.field) {
    if (auto sa = fastcast!(SelfAdding) (entry._1)) if (sa.addsSelf()) continue;
    sc.sup.add(entry._0, entry._1);
  }
  return fastcast!(Object) (sc._body);
}
mixin DefaultParser!(gotAutoDecl, "tree.stmt.autodecl", "22");
