module ast.withstmt;

import ast.base, ast.parse, ast.vardecl, ast.namespace, ast.guard, ast.scopes, ast.fun, ast.casting, ast.assign;

RelNamespace myresolve(RelNamespace rn) {
  if (auto wa = fastcast!(WithAware) (rn)) return fastcast!(RelNamespace) (wa.forWith());
  return rn;
}

Namespace myresolve(Namespace ns) {
  if (auto wa = fastcast!(WithAware) (ns)) return fastcast!(Namespace) (wa.forWith());
  return ns;
}

bool same(Object a, Object b) {
  if (a is b) return true;
  {
    auto os1 = fastcast!(OverloadSet) (a), os2 = fastcast!(OverloadSet) (b);
    if (os1 && os2) {
      if (os1.name != os2.name) return false;
      if (os1.funs.length != os2.funs.length) return false;
      foreach (i, f1; os1.funs) if (f1 !is os2.funs[i]) return false;
      return true;
    }
  }
  return false;
}

class WithStmt : Namespace, Statement, ScopeLike {
  RelNamespace rns;
  Stuple!(RelNamespace, Expr) [] rnslist;
  Namespace ns;
  VarDecl vd;
  Expr context;
  Scope sc;
  IScoped isc;
  mixin defaultIterate!(vd, sc);
  override WithStmt dup() {
    auto res = new WithStmt;
    res.rns = rns; res.rnslist = rnslist;
    res.ns = ns; res.vd = vd; res.context = context.dup;
    res.sc = sc.dup;
    res.isc = isc;
    res.temps = temps;
    return res;
  }
  mixin DefaultScopeLikeGuards!();
  string toString() { return Format("with ("[], context, ") <- "[], sup); }
  int temps;
  override int framesize() {
    auto supsz = (fastcast!(ScopeLike) (sup)).framesize();
    if (supsz == -1) return -1;
    return supsz + temps;
  }
  this(Expr ex) {
    sup = namespace();
    namespace.set(this);
    scope(exit) namespace.set(this.sup);
    
    sc = new Scope;
    assert(!!sc.sup);
    
    namespace.set(sc);
    
    if (auto isc = fastcast!(IScoped) (ex)) {
      this.isc = isc;
      ex = isc.getSup;
      auto vt = ex.valueType();
      
      auto backupvar = fastalloc!(Variable)(vt, cast(string) null, ex, boffs(vt));
      sc.add(backupvar);
      sc.addStatement(fastalloc!(VarDecl)(backupvar));
      sc.addGuard(mkAssignment(ex, backupvar));
      if (auto aex = isc.getAssign())
        sc.addStatement(mkAssignment(ex, aex));
      
      assert(!!fastcast!(LValue) (ex) || !!fastcast!(MValue) (ex), Format(ex, " which is ", isc, ".getSup; is not an LValue/MValue. Halp. "));
    }
    
    if (auto lv = fastcast!(LValue)~ ex) {
      context = lv;
    } else if (auto mv = fastcast!(MValue)~ ex) {
      context = mv;
    } else if (ex.valueType() == Single!(Void)) {
      context = ex; // hackaround :)
    } else {
      auto var = new Variable;
      var.type = ex.valueType();
      var.initval = ex;
      var.baseOffset = boffs(var.type);
      temps += var.type.size;
      context = var;
      sc.addStatement(fastalloc!(VarDecl)(var));
    }
    
    ex = context;
    
    if (!isc) { // IScoped does not do implicit namespace merge!
      rns = fastcast!(RelNamespace) (ex.valueType());
      
      if (auto srns = fastcast!(SemiRelNamespace) (ex.valueType())) rns = srns.resolve();
      ns = fastcast!(Namespace) (ex); // say, context
    }
    
    if (!rns && !ns && !isc) {
      Expr ex2 = context;
      auto backup = namespace();
      namespace.set(sup);
      scope(exit) namespace.set(backup);
      
      while (true) {
        auto ex3 = ex2;
        gotImplicitCast(ex3, (Expr ex) {
          auto it = ex.valueType();
          if (auto ns = fastcast!(RelNamespace)~ it)
            rnslist ~= stuple(ns, ex);
          return false;
        });
        if (fastcast!(Pointer) (ex2.valueType())) {
          ex2 = fastalloc!(DerefExpr)(ex2);
          continue;
        }
        break;
      }
      if (!rnslist) {
        logln("Cannot with-expr a non-[rel]ns: ", context); // TODO: select in gotWithStmt
        fail;
      }
    }
    
    if (auto onUsing = iparse!(Statement, "onUsing", "tree.semicol_stmt.expr", canFail)
                              ("evaluate ex.onUsing", "ex"[], context))
      sc.addStatement(onUsing);
    
    if (auto onExit = iparse!(Statement, "onExit", "tree.semicol_stmt.expr", canFail)
                              ("evaluate ex.onExit", "ex"[], context))
      sc.addGuard(onExit);
    if (rns) rns = myresolve(rns);
    if (rnslist)
      foreach (ref rns; rnslist)
        rns._0 = myresolve(rns._0);
    if (ns) ns = myresolve(ns);
  }
  private this() { }
  override {
    void emitAsm(AsmFile af) {
      assert(false); // see below: "shortcut"
    }
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() {
      auto res = sup.stackframe();
      if (vd)
        res ~= stuple(vd.var.type, vd.var.name, vd.var.baseOffset);
      if (temps) {
        auto var = fastcast!(Variable) (context);
        res ~= stuple(var.type, var.name, var.baseOffset);
      }
      return res;
    }
    Object lookup(string name, bool local = false) {
      if (name == "that") return fastcast!(Object)~ context;
      bool block;
      /* already have "that" to accomplish this */
      if (name == "this") block = true;
      auto supres = sup.lookup(name, local);
      void checkShadow(Object res, Object containing) {
        if (!supres || same(res, supres)) return;
        if (fastcast!(ISafeSpaceTag) (containing)) return;
        auto ex = new Exception(Format(
          "Use of '", name, "' shadows outside identifier. "
          "Please disambiguate using '.', 'this' or 'that'."
          // "\nThe shadowed value is : '", supres, "'.\n"
          // "\nThe local value is    : '", res, "'. \n"
        ));
        // logln(ex); fail;
        throw ex;
      }
      if (!local && !block) {
        if (rns)
          if (auto res = rns.lookupRel(name, context, false)) {
            checkShadow(res, fastcast!(Object) (rns));
            return res;
          }
        if (rnslist)
          foreach (rns; rnslist)
            if (auto res = rns._0.lookupRel(name, rns._1, false)) {
              checkShadow(res, fastcast!(Object) (rns._0));
              return res;
            }
        if (ns)
          if (auto res = ns.lookup(name, true)) {
            checkShadow(res, fastcast!(Object) (ns));
            return res;
          }
      }
      return sup.lookup(name, local);
    }
  }
}

import tools.log, ast.tuple_access, ast.pointer;
Object gotWithStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  string t3;
  if (!(rest(t2, "tree.expr _tree.expr.arith", &ex) && ( t3 = t2, true ) && t3.accept("{")) && (t2 = text, true) && !rest(t2, "tree.expr", &ex))
    t2.failparse("Couldn't match with-expr");
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  // if (fastcast!(Pointer) (ex.valueType()))
  //   ex = fastalloc!(DerefExpr)(ex);
  
  WithStmt ws, outer;
  
  bool scoped;
  Expr newval;
  if (auto isc = fastcast!(IScoped) (ex)) {
    ex = isc.getSup;
    newval = isc.getAssign();
    scoped = true;
  }
  
  if (auto list = getTupleEntries(ex)) {
    Expr[] list2;
    if (newval) {
      list2 = getTupleEntries(newval);
      if (list2.length != list.length) t2.failparse("Bad assignment list for tuple-with");
    }
    foreach (i, entry; list) {
      if (scoped) {
        Expr e2;
        if (list2) e2 = list2[i];
        entry = genScoped(entry, e2);
      }
      
      auto prev = ws;
      try ws = fastalloc!(WithStmt)(entry);
      catch (Exception ex) t2.failparse(ex);
      ws.sc.configPosition(t2);
      if (!outer) outer = ws;
      namespace.set(ws.sc);
      if (prev) prev.sc.addStatement(ws.sc /* shortcut */);
    }
  } else {
    if (scoped) ex = genScoped(ex, newval);
    try ws = fastalloc!(WithStmt)(ex);
    catch (Exception ex) t2.failparse(ex);
    ws.sc.configPosition(t2);
    outer = ws;
    namespace.set(ws.sc);
  }
  Statement st;
  if (!rest(t2, "tree.stmt"[], &st))
    t2.failparse("Couldn't match with-body");
  ws.sc.addStatement(st);
  text = t2;
  return outer;
}
mixin DefaultParser!(gotWithStmt, "tree.stmt.withstmt", "11", /*"with"*/"using");

Object gotBackupOf(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (t2.gotIdentifier(name) && t2.accept(")")) {
    auto ws = namespace().get!(WithStmt);
    string[] names;
    do {
      if (!ws.isc) continue;
      auto n = fastcast!(Named)~ ws.isc.getSup();
      if (!n) continue;
      auto ident = n.getIdentifier();
      if (ident == name)
        return ws.vd.var;
      names ~= ident;
    } while (test(ws = ws.get!(WithStmt)));
    throw new Exception(Format("No backup for ", name, ", only ", names, ". "));
  } else
    t2.failparse("Failed to parse backupof()");
}
mixin DefaultParser!(gotBackupOf, "tree.expr.backupof", "52", "backupof(");
