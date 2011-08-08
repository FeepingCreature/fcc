module ast.withstmt;

import ast.base, ast.parse, ast.vardecl, ast.namespace, ast.guard, ast.scopes, ast.fun, ast.casting, ast.assign;

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
  override Statement[] getGuards() {
    if (auto sl = fastcast!(ScopeLike) (sup))
      return sl.getGuards();
    else
      return null;
  }
  string toString() { return Format("with (", context, ") <- ", sup); }
  int temps;
  override int framesize() {
    return (fastcast!(ScopeLike)~ sup).framesize() + temps;
  }
  this(Expr ex) {
    sup = namespace();
    namespace.set(this);
    scope(exit) namespace.set(this.sup);
    
    sc = new Scope;
    assert(!!sc.sup);
    
    if (auto isc = fastcast!(IScoped) (ex)) {
      this.isc = isc;
      ex = isc.getSup;
      auto vt = ex.valueType();
      
      auto backupvar = new Variable(vt, null, ex, boffs(vt));
      sc.add(backupvar);
      
      auto vd = new VarDecl;
      vd.vars ~= backupvar;
      sc.addStatement(vd);
      sc.addGuard(mkAssignment(ex, backupvar));
      assert(!!fastcast!(LValue) (ex) || !!fastcast!(MValue) (ex), Format(ex, " which is ", isc, ".getSup; is not an LValue/MValue. Halp. "));
    }
    
    if (auto lv = fastcast!(LValue)~ ex) {
      context = lv;
    } else if (auto mv = fastcast!(MValue)~ ex) {
      context = mv;
    } else {
      auto var = new Variable;
      var.type = ex.valueType();
      var.initval = ex;
      var.baseOffset = boffs(var.type);
      temps += var.type.size;
      context = var;
      New(vd);
      vd.vars ~= var;
      sc.addStatement(vd);
    }
    
    rns = fastcast!(RelNamespace)~ ex.valueType();
    
    if (auto srns = fastcast!(SemiRelNamespace) (ex.valueType())) rns = srns.resolve();
    ns = fastcast!(Namespace)~ ex; // say, context
    
    if (!rns && !ns && !isc) {
      Expr ex2 = context;
      auto backup = namespace();
      namespace.set(sup);
      scope(exit) namespace.set(backup);
      
      gotImplicitCast(ex2, (Expr ex) {
        auto it = ex.valueType();
        if (auto ns = fastcast!(RelNamespace)~ it)
          rnslist ~= stuple(ns, ex);
        return false;
      });
      if (!rnslist) {
        logln("Cannot with-expr a non-[rel]ns: ", context); // TODO: select in gotWithStmt
        asm { int 3; }
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
    void emitC(CFile cf) { sc.emitC(cf); }
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() {
      auto res = sup.stackframe();
      if (vd)
        foreach (var; vd.vars)
          res ~= stuple(var.type, var.name, var.baseOffset);
      return res;
    }
    Object lookup(string name, bool local = false) {
      if (name == "that") return fastcast!(Object)~ context;
      bool block;
      /* already have "that" to accomplish this */
      if (name == "this") block = true;
      if (!local && !block) {
        if (rns)
          if (auto res = rns.lookupRel(name, context))
            return res;
        if (rnslist)
          foreach (rns; rnslist)
            if (auto res = rns._0.lookupRel(name, rns._1))
              return res;
        if (ns)
          if (auto res = ns.lookup(name, true))
            return res;
      }
      return sup.lookup(name);
    }
  }
}

import tools.log, ast.tuple_access, ast.pointer;
Object gotWithStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex))
    t2.failparse("Couldn't match with-expr");
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  if (fastcast!(Pointer) (ex.valueType()))
    ex = new DerefExpr(ex);
  
  WithStmt ws, outer;
  
  bool scoped;
  if (auto isc = fastcast!(IScoped) (ex)) {
    ex = isc.getSup;
    scoped = true;
  }
  
  if (auto list = getTupleEntries(ex)) {
    foreach (entry; list) {
      if (scoped) entry = genScoped(entry);
      
      auto prev = ws;
      ws = new WithStmt(entry);
      ws.sc.configPosition(t2);
      if (!outer) outer = ws;
      namespace.set(ws.sc);
      if (prev) prev.sc.addStatement(ws);
    }
  } else {
    if (scoped) ex = genScoped(ex);
    ws = new WithStmt(ex);
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
        return ws.vd.vars[0];
      names ~= ident;
    } while (test(ws = ws.get!(WithStmt)));
    throw new Exception(Format("No backup for ", name, ", only ", names, ". "));
  } else
    t2.failparse("Failed to parse backupof()");
}
mixin DefaultParser!(gotBackupOf, "tree.expr.backupof", "52", "backupof(");
