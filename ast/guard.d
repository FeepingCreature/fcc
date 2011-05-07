module ast.guard;

import
  ast.parse, ast.base, ast.namespace, ast.scopes,
  ast.assign, ast.nestfun, ast.modules,
  ast.variable, ast.vardecl;

Object gotGuard(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string type;
  if (t2.accept("onExit")) type = "onExit";
  else if (t2.accept("onSuccess")) type = "onSuccess";
  else if (t2.accept("onFailure")) type = "onFailure";
  else return null;
  Statement st1, st2;
  auto t3 = t2, t4 = t2;
  auto sc = namespace().get!(Scope)();
  assert(!!sc, Format("::", namespace()));
  
  if (type == "onSuccess" || type == "onExit") {
    pushCache;
    scope(exit) popCache;
    if (!rest(t3, "tree.stmt", &st1))
      t3.failparse("No statement matched for ", type, " in scope context");
    sc.guards ~= st1;
  }
  if (type == "onFailure" || type == "onExit") {
    auto nf = new NestedFunction(sc), mod = current_module();
    New(nf.type);
    nf.type.ret = Single!(Void);
    nf.fixup;
    nf.sup = mod;
    static int funId;
    synchronized
      nf.name = Format("guardfn_", funId++);
    {
      pushCache;
      scope(exit) popCache;
      auto backup = namespace();
      scope(exit) namespace.set(backup);
      namespace.set(nf);
      if (!rest(t4, "tree.scope", &st2))
        t4.failparse("No statement matched for ", type, " in exception guard context");
      nf.tree = st2;
    }
    mod.entries ~= fastcast!(Tree) (nf);
    auto grtype = fastcast!(IType)~ sysmod.lookup("_GuardRecord");
    assert(!!grtype);
    {
      auto gr = new Variable(grtype, null, boffs(grtype));
      gr.initInit;
      auto decl = new VarDecl;
      decl.vars ~= gr;
      sc.addStatement(decl);
      auto sl = namespace().get!(ScopeLike);
      namespace().add(gr);
      {
        auto setup_st =
          iparse!(Statement, "gr_setup_1", "tree.stmt")
                 (`
                 {
                   var.dg = &fun;
                   var.prev = _record;
                   _record = &var;
                 }`,
                 "var", gr, "fun", nf);
        assert(!!setup_st);
        sc.addStatement(setup_st);
      }
      {
        auto setup_st =
          iparse!(Statement, "gr_setup_2", "tree.stmt")
                 (`onSuccess _record = _record.prev; `, namespace());
        assert(!!setup_st);
        // no need to add, is NoOp
      }
    }
  }
  if (st1 && st2 && st1 is st2) {
		t2.failparse("Failed to produce different sts! ");
  }
  
  t3.passert(type != "onExit" || t3 is t4,
    "Mismatch: First case matched to '", t3.nextText(), "', "
           "second to '", t4.nextText(), "'. "
  );
  text = t3;
  return Single!(NoOp);
}
mixin DefaultParser!(gotGuard, "tree.stmt.guard", "17");

interface IScoped {
  Expr getSup();
}

import ast.tuples: LValueAsMValue;
class Scoped(T) : T, IScoped {
  T sup;
  static assert(is(T: LValue) || is(T: MValue));
  this(T t) { sup = t; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(sup);
  override {
    void emitAsm(AsmFile af) { assert(false); }
    IType valueType() { return sup.valueType(); }
    Expr getSup() { return sup; }
    static if (is(T: LValue)) {
      void emitLocation(AsmFile af) { assert(false); }
    }
    static if (is(T: MValue)) {
      void emitAssignment(AsmFile af) { assert(false); }
    }
  }
}

Expr genScoped(Expr ex) {
  if (auto mv = fastcast!(MValue)~ ex) return new Scoped!(MValue)(mv);
  if (auto lv = fastcast!(LValue)~ ex) return new Scoped!(LValue)(lv);
  throw new Exception(Format("cannot scope ", ex));
}

import tools.log;
Object gotScoped(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex))
    t2.failparse("Failed to match expr for scoped");
  text = t2;
  return fastcast!(Object)~ genScoped(ex);
}
mixin DefaultParser!(gotScoped, "tree.expr.scoped", "26", "scoped");
