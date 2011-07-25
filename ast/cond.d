// conditions
module ast.cond;

import
  ast.base, ast.parse, ast.oop, ast.namespace, ast.modules, ast.vardecl,
  ast.variable, ast.scopes, ast.nestfun, ast.casting, ast.arrays,
  ast.aliasing, ast.fun;
// I'm sorry this is so ugly.
Object gotHdlStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  IType it;
  if (!t2.accept("(") || !rest(t2, "type", &it))
    t2.failparse("opening paren followed by type expected");
  assert(fastcast!(ClassRef)~ it || fastcast!(IntfRef)~ it);
  string pname;
  t2.gotIdentifier(pname);
  if (!t2.accept(")"))
    t2.failparse("closing paren expected");
  IType hdltype = fastcast!(IType) (sysmod.lookup("_Handler")), objtype = fastcast!(ClassRef) (sysmod.lookup("Object"));
  string hdlmarker = Format("__hdlmarker_var_special_", getuid());
  assert(!namespace().lookup(hdlmarker));
  auto hdlvar = new Variable(hdltype, hdlmarker, boffs(hdltype));
  hdlvar.initInit;
  auto decl = new VarDecl;
  decl.vars ~= hdlvar;
  auto csc = fastcast!(Scope)~ namespace();
  assert(!!csc);
  csc.addStatement(decl);
  csc.add(hdlvar);
  auto nf = new NestedFunction(csc), mod = current_module();
  New(nf.type);
  nf.type.ret = Single!(Void);
  nf.type.params ~= Argument(objtype, "_obj");
  static int hdlId;
  synchronized
    nf.name = Format("hdlfn_", hdlId++);
  nf.fixup;
  nf.sup = mod;
  mod.entries ~= fastcast!(Tree)~ nf;
  {
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(nf);
    
    auto sc = new Scope;
    sc.configPosition(t2);
    nf.tree = sc;
    namespace.set(sc);
    
    auto objvar = new Variable(it, null, boffs(it));
    objvar.initval = reinterpret_cast(it, fastcast!(Expr)~ nf.lookup("_obj", true));
    auto decl2 = new VarDecl;
    decl2.vars ~= objvar;
    sc.addStatement(decl2);
    sc.add(objvar);
    {
      auto ea = new ExprAlias(objvar, pname);
      sc.add(ea);
    }
    auto nf2 = new NestedFunction(sc);
    with (nf2) {
      New(type);
      type.ret = Single!(Void);
      type.params ~= Argument(Single!(Array, Single!(Char)), "n");
      fixup;
      name = "invoke-exit";
      auto backup2 = namespace();
      scope(exit) namespace.set(backup2);
      namespace.set(nf2);
      nf2.tree = iparse!(Statement, "cond_nest", "tree.stmt") // can't use hdlvar here, because it's in the wrong scope
                        (`_lookupCM(n, &hdlvar, true).jump();`, namespace(), "hdlvar", lookup(hdlmarker));
      hdlvar.name = null; // marker string not needed
    }
    mod.entries ~= fastcast!(Tree)~ nf2;
    sc.add(nf2);
    
    Scope sc2;
    if (!rest(t2, "tree.scope", &sc2))
      t2.failparse("No statement matched in handler context");
    sc.addStatement(sc2);
  }
  {
    auto setup_st =
      iparse!(Statement, "gr_setup_1", "tree.stmt")
             (`
             {
               var.id = class-id type;
               var.prev = __hdl__;
               var.dg = &fn;
               var.delimit = _cm;
               __hdl__ = &var;
             }`,
             "var", hdlvar, "type", it, "fn", nf);
    assert(!!setup_st);
    csc.addStatement(setup_st);
  }
  {
    auto guard_st =
      iparse!(Statement, "hdl_undo", "tree.stmt")
              (`onSuccess __hdl__ = __hdl__.prev; `, csc);
    assert(!!guard_st);
    // again, no need to add (is NoOp)
  }
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotHdlStmt, "tree.stmt.hdl", "18", "set-handler");

import ast.ifstmt;
Object gotExitStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  Expr ex;
  bool isString(IType it) { return test(it == Single!(Array, Single!(Char))); }
  if (!rest(t2, "tree.expr", &ex) || !gotImplicitCast(ex, &isString))
    assert(false);
  IType cmtype = fastcast!(IType)~ sysmod.lookup("_CondMarker");
  auto cmvar = new Variable(cmtype, null, boffs(cmtype));
  cmvar.initInit;
  auto decl = new VarDecl;
  decl.vars ~= cmvar;
  auto csc = fastcast!(Scope)~ namespace();
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
    assert(!!setup_st);
    csc.addStatement(setup_st);
  }
  {
    auto guard_st =
      iparse!(Statement, "cm_undo", "tree.stmt")
             (`onSuccess _cm = (_CondMarker*:_cm).prev; `, csc);
    assert(!!guard_st);
  }
  auto ifs = new IfStatement;
  ifs.wrapper = new Scope;
  ifs.test = iparse!(Cond, "cm_cond", "cond")
                    (`setjmp &(var.target)`,
                     "var", cmvar);
  assert(!!ifs.test);
  configure(ifs.test);
  if (!rest(t2, "tree.scope", &ifs.branch1))
    t2.failparse("Couldn't get cond_exit branch");
  text = t2;
  return ifs;
}
mixin DefaultParser!(gotExitStmt, "tree.stmt.cond_exit", "181", "define-exit");
