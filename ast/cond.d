// conditions
module ast.cond;

import
  ast.base, ast.parse, ast.oop, ast.namespace, ast.modules, ast.vardecl,
  ast.variable, ast.scopes, ast.nestfun, ast.casting, ast.arrays;
// I'm sorry this is so ugly.
Object gotHdlStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  if (!t2.accept("set-handler"))
    return null;
  IType it;
  if (!t2.accept("(") || !rest(t2, "type", &it))
    assert(false);
  assert(cast(ClassRef) it || cast(IntfRef) it);
  string pname;
  t2.gotIdentifier(pname);
  if (!t2.accept(")"))
    assert(false);
  IType hdltype = cast(IType) sysmod.lookup("_Handler"), objtype = new ClassRef(cast(Class) sysmod.lookup("Object"));
  const string hdlmarker = "__hdlmarker_var_special";
  assert(!namespace().lookup(hdlmarker));
  auto hdlvar = new Variable(hdltype, hdlmarker, boffs(hdltype));
  hdlvar.initInit;
  auto decl = new VarDecl;
  decl.vars ~= hdlvar;
  auto csc = cast(Scope) namespace();
  assert(!!csc);
  csc.addStatement(decl);
  csc.add(hdlvar);
  auto nf = new NestedFunction(csc), mod = csc.get!(Module)();
  New(nf.type);
  nf.type.ret = Single!(Void);
  nf.type.params ~= stuple(objtype, "_obj");
  nf.fixup;
  static int hdlId;
  nf.name = Format("hdlfn_", hdlId++);
  mod.entries ~= cast(Tree) nf;
  {
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(nf);
    auto sc = new Scope;
    nf.tree = sc;
    namespace.set(sc);
    auto objvar = new Variable(it, null, boffs(it));
    objvar.initval = reinterpret_cast(it, cast(Expr) nf.lookup("_obj"));
    auto decl2 = new VarDecl;
    decl2.vars ~= objvar;
    sc.addStatement(decl2);
    sc.add(objvar);
    auto nf2 = new NestedFunction(sc);
    with (nf2) {
      New(type);
      type.ret = Single!(Void);
      type.params ~= stuple(cast(IType) Single!(Array, Single!(Char)), "n");
      fixup;
      name = "_invokeExit";
      auto backup2 = namespace();
      scope(exit) namespace.set(backup2);
      namespace.set(nf2);
      nf2.tree = iparse!(Statement, "cond_nest", "tree.stmt")
                        (`_lookupCM(n, &`~hdlmarker~`).jump();`, namespace());
      hdlvar.name = null; // marker string not needed
    }
    mod.entries ~= cast(Tree) nf2;
    sc.add(nf2);
    auto sl = namespace().get!(ScopeLike)();
    Scope sc2;
    if (!rest(t2, "tree.scope", &sc2))
      throw new Exception("No statement matched in handler context: "~t2.next_text());
    sc.addStatement(sc2);
  }
  {
    auto setup_st =
      iparse!(Statement, "gr_setup_1", "tree.stmt")
             (`
             {
               var.id = type.classid;
               var.prev = __hdl__;
               var.dg = &fn;
               var.delimit = _cm;
               __hdl__ = &var;
             }`,
             "var", hdlvar, "type", it, "fn", nf);
    assert(setup_st);
    csc.addStatement(setup_st);
  }
  {
    auto guard_st =
      iparse!(Statement, "hdl_undo", "tree.stmt")
              (`onSuccess __hdl__ = __hdl__.prev; `, csc);
    assert(guard_st);
    // again, no need to add (is NoOp)
  }
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotHdlStmt, "tree.stmt.hdl", "18");

import ast.ifstmt;
Object gotExitStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  if (!t2.accept("define-exit"))
    return null;
  Expr ex;
  bool isString(IType it) { return test(it == Single!(Array, Single!(Char))); }
  if (!rest(t2, "tree.expr", &ex) || !gotImplicitCast(ex, &isString))
    assert(false);
  IType cmtype = cast(IType) sysmod.lookup("_CondMarker");
  auto cmvar = new Variable(cmtype, null, boffs(cmtype));
  cmvar.initInit;
  auto decl = new VarDecl;
  decl.vars ~= cmvar;
  auto csc = cast(Scope) namespace();
  assert(!!csc);
  csc.addStatement(decl);
  csc.add(cmvar);
  {
    auto setup_st =
      iparse!(Statement, "hdl_setup", "tree.stmt")
             (`
             {
               var.prev = _cm;
               var.name = nex;
               if (_record) var.guard_id = _record.dg;
               var.old_hdl = __hdl__;
               _cm = &var;
             }`,
             "var", cmvar, "nex", ex);
    assert(setup_st);
    csc.addStatement(setup_st);
  }
  {
    auto guard_st =
      iparse!(Statement, "cm_undo", "tree.stmt")
             (`onSuccess _cm = _cm.prev; `, csc);
    assert(guard_st);
  }
  auto ifs = new IfStatement;
  ifs.test = iparse!(Cond, "cm_cond", "cond")
                    (`setjmp var.target`,
                     "var", cmvar);
  assert(!!ifs.test);
  configure(ifs.test);
  if (!rest(t2, "tree.scope", &ifs.branch1))
    throw new Exception("Couldn't get if branch at "~t2.next_text());
  text = t2;
  return ifs;
}
mixin DefaultParser!(gotExitStmt, "tree.stmt.cond_exit", "181");
