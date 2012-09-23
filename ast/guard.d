module ast.guard;

import
  ast.parse, ast.base, ast.namespace, ast.scopes,
  ast.assign, ast.nestfun, ast.modules,
  ast.variable, ast.vardecl, ast.fun,
  ast.aliasing;

Object gotGuard(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string type;
  if (t2.accept("onExit"[])) type = "onExit";
  else if (t2.accept("onSuccess"[])) type = "onSuccess";
  else if (t2.accept("onFailure"[])) type = "onFailure";
  else return null;
  
  auto ns = namespace();
  
  string[] captures;
  Variable[] capturevars;
  if (t2.accept("["[])) {
    while (true) {
      if (t2.accept("]"[])) break;
      if (captures.length && !t2.accept(","[]))
        t2.failparse("comma expected (capture must be identifier)"[]);
      string id;
      if (!gotIdentifier(t2, id))
        t2.failparse("capture identifier expected"[]);
      captures ~= id;
      
      auto ex = fastcast!(Expr) (ns.lookup(id));
      if (!ex) t2.failparse("Unknown identifier '"~id~"' for capture, or not expression"[]);
      auto ty = ex.valueType();
      auto var = fastalloc!(Variable)(ty, cast(string) null, boffs(ty));
      
      auto sc = ns.get!(Scope);
      if (!sc) {
        t2.failparse("No scope found at "[], namespace(), " for inserting capture variable"[]);
      }
      sc.addStatement(fastalloc!(VarDecl)(var, ex));
      ns.add(var);
      capturevars ~= var;
    }
  }
  
  auto ms = fastalloc!(MiniNamespace)("captures_holder"[]);
  ms.sup = ns;
  ms.internalMode = true;
  namespace.set(ms);
  scope(exit) namespace.set(ms.sup);
  foreach (i, cap; captures) {
    ms.add(cap, fastalloc!(LValueAlias)(capturevars[i], cap));
  }
  ms.internalMode = false;
  
  Statement st1, st2;
  auto t3 = t2, t4 = t2;
  auto sc = namespace().get!(Scope);
  if (!sc) { logln("::"[], namespace()); fail; }
  
  if (type == "onSuccess" || type == "onExit"[]) {
    auto popCache = pushCache(); scope(exit) popCache();
    genRetvalHolder(sc);
    if (!rest(t3, "tree.stmt"[], &st1))
      t3.failparse("No statement matched for "[], type, " in scope context"[]);
    sc.addGuard(st1);
  }
  if (type == "onFailure" || type == "onExit"[]) {
    auto nf = fastalloc!(NestedFunction)(sc), mod = fastcast!(Module) (current_module());
    New(nf.type);
    nf.type.ret = Single!(Void);
    nf.sup = mod;
    static int funId;
    synchronized
      nf.name = Format("guardfn_"[], funId++);
    {
      auto popCache = pushCache(); scope(exit) popCache();
      auto backup = namespace();
      scope(exit) namespace.set(backup);
      namespace.set(nf);
      nf.fixup;
      
      if (!rest(t4, "tree.scope"[], &st2))
        t4.failparse("No statement matched for "[], type, " in exception guard context"[]);
      nf.addStatement(st2);
    }
    mod.entries ~= fastcast!(Tree) (nf);
    auto grtype = fastcast!(IType)~ sysmod.lookup("_GuardRecord"[]);
    assert(!!grtype);
    {
      auto gr = fastalloc!(Variable)(grtype, cast(string) null, boffs(grtype));
      auto gd = fastalloc!(VarDecl)(gr);
      gd.initInit;
      sc.addStatement(gd);
      auto sl = namespace().get!(ScopeLike);
      namespace().add(gr);
      {
        auto setup_st =
          iparse!(Statement, "gr_setup_1"[], "tree.stmt"[])
                 (`
                 {
                   var.dg = &fun;
                   var.prev = _record;
                   _record = &var;
                 }`,
                 "var"[], gr, "fun"[], nf);
        assert(!!setup_st);
        sc.addStatement(setup_st);
      }
      {
        auto setup_st =
          iparse!(Statement, "gr_setup_2"[], "tree.stmt"[])
                 (`onSuccess _record = _record.prev; `, namespace());
        assert(!!setup_st);
        // no need to add, is NoOp
      }
    }
  }
  if (st1 && st2 && st1 is st2) {
		t2.failparse("Failed to produce different sts! "[]);
  }
  
  t3.passert(type != "onExit" || t3 is t4,
    "Mismatch: First case matched to '"[], t3.nextText(), "', "
           "second to '"[], t4.nextText(), "'. "
  );
  if (type == "onFailure"[]) text = t4;
  else text = t3;
  return Single!(NoOp);
}
mixin DefaultParser!(gotGuard, "tree.stmt.guard"[], "17"[]);

interface IScoped {
  Expr getSup();
  Expr getAssign();
}

import ast.tuples: LValueAsMValue;
class Scoped(T) : T, IScoped {
  T sup;
  Expr newval;
  static assert(is(T: LValue) || is(T: MValue));
  this(T t, Expr newval) { sup = t; this.newval = newval; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(sup);
  override {
    void emitAsm(AsmFile af) { assert(false); }
    IType valueType() { return sup.valueType(); }
    Expr getSup() { return sup; }
    Expr getAssign() { return newval; }
    static if (is(T: LValue)) {
      void emitLocation(AsmFile af) { assert(false); }
    }
    static if (is(T: MValue)) {
      void emitAssignment(AsmFile af) { assert(false); }
    }
  }
}

Expr genScoped(Expr ex, Expr newval = null) {
  if (auto sc = namespace().get!(Scope)) genRetvalHolder(sc); // make sure we can place the ensuing scope gard properly
  else { logln("uh-oh "[], namespace()); fail; }
  if (auto mv = fastcast!(MValue) (ex)) return new Scoped!(MValue)(mv, newval);
  if (auto lv = fastcast!(LValue) (ex)) return new Scoped!(LValue)(lv, newval);
  throw new Exception(Format("cannot scope "[], ex));
}

import tools.log;
Object gotScoped(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex, newval;
  if (!rest(t2, "tree.expr"[], &ex))
    t2.failparse("Failed to match expr for scoped"[]);
  if (t2.accept("="[])) {
    if (!rest(t2, "tree.expr"[], &newval))
      t2.failparse("Failed to match new-value expr for scoped"[]);
  }
  text = t2;
  return fastcast!(Object) (genScoped(ex, newval));
}
mixin DefaultParser!(gotScoped, "tree.expr.scoped"[], "26"[], "scoped"[]);
