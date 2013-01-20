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

import ast.structure;
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
    res.sup = namespace();
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(res);
    
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
      
      if (auto rns = fastcast!(RelNamespace)(isc)) { // for adding stuff like commit/rollback
        rnslist ~= stuple(rns, ex);
      }
      
      // genRetvalHolder(sc);
      auto backupvar = fastalloc!(Variable)(vt, framelength(), cast(string) null);
      isc.setBackupVar(backupvar);
      sc.add(backupvar);
      sc.addStatement(fastalloc!(VarDecl)(backupvar, ex));
      sc.addGuard(mkAssignment(ex, backupvar));
      if (auto aex = isc.getAssign())
        sc.addStatement(mkAssignment(ex, aex));
      
      assert(!!fastcast!(LValue) (ex) || !!fastcast!(MValue) (ex), Format(ex, " which is ", isc, ".getSup; is not an LValue/MValue. Halp. "));
    }
    
    auto mv = fastcast!(MValue)(ex);
    
    if (auto lv = fastcast!(LValue)~ ex) {
      context = lv;
    } else if (mv && !fastcast!(Structure)(resolveType(ex.valueType()))) {
      context = mv;
    } else if (ex.valueType() == Single!(Void)) {
      context = ex; // hackaround :)
    } else {
      auto var = fastalloc!(Variable)(ex.valueType(), framelength(), cast(string) null);;
      temps ++;
      context = var;
      sc.addStatement(fastalloc!(VarDecl)(var, ex));
    }
    
    ex = context;
    
    if (!isc) { // IScoped does its own namespace merge
      rns = fastcast!(RelNamespace) (ex.valueType());
      
      if (auto srns = fastcast!(SemiRelNamespace) (ex.valueType())) rns = srns.resolve();
      ns = fastcast!(Namespace) (ex); // say, context
      
      Expr ex2 = context;
      auto backup = namespace();
      namespace.set(sup);
      scope(exit) namespace.set(backup);
      
      while (true) {
        auto ex3 = ex2;
        gotImplicitCast(ex3, (Expr ex) {
          auto it = resolveType(ex.valueType());
          auto rns = fastcast!(RelNamespace) (it);
          if (auto srns = fastcast!(SemiRelNamespace) (it)) rns = srns.resolve();
          if (rns) rnslist ~= stuple(rns, reinterpret_cast(it, ex));
          return false;
        }, false);
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
    
    if (showsAnySignOfHaving(context, "onUsing")) {
      if (auto onUsing = iparse!(Expr, "onUsing", "tree.expr", canFail)
                                ("evaluate ex.onUsing"[], "ex"[], context))
        sc.addStatement(new ExprStatement(onUsing));
    }
    
    if (showsAnySignOfHaving(context, "onExit")) {
      if (auto onExit = iparse!(Expr, "onExit", "tree.expr", canFail)
                                ("evaluate ex.onExit"[], "ex"[], context))
        sc.addGuard(new ExprStatement(onExit));
    }
    
    if (rns) rns = myresolve(rns);
    if (rnslist)
      foreach (ref rns; rnslist)
        rns._0 = myresolve(rns._0);
    if (ns) ns = myresolve(ns);
  }
  private this() { }
  override {
    void emitLLVM(LLVMFile lf) {
      mixin(mustOffset("0"));
      sc.emitLLVM(lf);
    }
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string)[] stackframe() {
      if (!sup) {
        logln("No sup beneath ", this);
        fail;
      }
      auto res = sup.get!(ScopeLike).stackframe();
      if (vd)
        res ~= stuple(vd.var.type, vd.var.name);
      if (temps) {
        auto var = fastcast!(Variable) (context);
        res ~= stuple(var.type, var.name);
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
          "\nThe shadowed value is : '", supres, "'."
          "\nThe local value is    : '", res, "'."
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
          foreach (rns; rnslist) {
            if (auto res = rns._0.lookupRel(name, rns._1, false)) {
              checkShadow(res, fastcast!(Object) (rns._0));
              return res;
            }
          }
        if (ns)
          if (auto res = ns.lookup(name, true)) {
            checkShadow(res, fastcast!(Object) (ns));
            return res;
          }
      }
      return supres;
    }
  }
}

import ast.enums;
class EnumWrapperType : RelNamespace, IType {
  Enum en;
  this(Enum en) { this.en = en; }
  override {
    string mangle() { return "enwrap_"~en.mangle(); }
    string llvmSize() { return "0"; }
    string llvmType() { return "{}"; }
    IType proxyType() { return null; }
    bool isPointerLess() { return true; }
    bool isComplete() { return true; }
    bool returnsInMemory() { return en.returnsInMemory(); }
    mixin TypeDefaults!(true);
    Object lookupRel(string name, Expr base, bool isDirectLookup = true) {
      if (base.valueType() !is this) {
        logln("assumefail ", base);
        fail;
      }
      return en.lookup(name);
    }
    bool isTempNamespace() { return true; }
  }
}

class EnumWrapper : Expr {
  Enum en;
  this(Enum en) { this.en = en; }
  mixin defaultIterate!();
  override {
    EnumWrapper dup() { return this; }
    IType valueType() { return fastalloc!(EnumWrapperType)(en); }
    void emitLLVM(LLVMFile lf) { push(lf, "void"); }
  }
}

import tools.log, ast.tuple_access, ast.pointer;
Object gotWithStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  IType it;
  string t3;
  if (rest(t2, "type", &it) && fastcast!(Enum) (it)) {
  } else if (rest(t2, "tree.expr _tree.expr.arith", &ex) &&
    (t3 = t2, true) && t3.accept("{")) {
  } else {
    t2 = text;
    if (rest(t2, "tree.expr", &ex)) {
    } else t2.failparse("Couldn't match with-expr or with-enum");
  }
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  if (auto en = fastcast!(Enum) (it)) {
    ex = fastalloc!(EnumWrapper)(en);
  }
  
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
  auto list = getTupleEntries(ex);
  if (list && !scoped /* scoped is not split */) {
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
      if (prev) prev.sc.addStatement(ws);
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
