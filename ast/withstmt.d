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
  string toString() { return Format("with (", context, ") <- ", sup); }
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
      
      auto backupvar = new Variable(vt, null, ex, boffs(vt));
      sc.add(backupvar);
      sc.addStatement(new VarDecl(backupvar));
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
      sc.addStatement(new VarDecl(var));
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
          ex2 = new DerefExpr(ex2);
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
                              ("evaluate ex.onUsing", "ex", context))
      sc.addStatement(onUsing);
    
    if (auto onExit = iparse!(Statement, "onExit", "tree.semicol_stmt.expr", canFail)
                              ("evaluate ex.onExit", "ex", context))
      sc.addGuard(onExit);
  }
  private this() { }
  override {
    void emitAsm(AsmFile af) {
      mixin(mustOffset("0"));
      sc.emitAsm(af);
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
      if (!local && !block) {
        if (rns)
          if (auto res = myresolve(rns).lookupRel(name, context, false))
            return res;
        if (rnslist)
          foreach (rns; rnslist)
            if (auto res = myresolve(rns._0).lookupRel(name, rns._1, false))
              return res;
        if (ns)
          if (auto res = myresolve(ns).lookup(name, true))
            return res;
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
  //   ex = new DerefExpr(ex);
  
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
      try ws = new WithStmt(entry);
      catch (Exception ex) t2.failparse(ex);
      ws.sc.configPosition(t2);
      if (!outer) outer = ws;
      namespace.set(ws.sc);
      if (prev) prev.sc.addStatement(ws);
    }
  } else {
    if (scoped) ex = genScoped(ex, newval);
    try ws = new WithStmt(ex);
    catch (Exception ex) t2.failparse(ex);
    ws.sc.configPosition(t2);
    outer = ws;
    namespace.set(ws.sc);
  }
  Statement st;
  if (!rest(t2, "tree.stmt", &st))
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
