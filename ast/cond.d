// conditions
module ast.cond;

import
  ast.base, ast.parse, ast.oop, ast.namespace, ast.modules, ast.vardecl,
  ast.variable, ast.scopes, ast.nestfun, ast.casting, ast.arrays,
  ast.aliasing, ast.fun, ast.literals, ast.pointer;
// I'm sorry this is so ugly.
Object gotHdlStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  IType it;
  if (!t2.accept("(") || !rest(t2, "type"[], &it))
    t2.failparse("opening paren followed by type expected"[]);
  assert(fastcast!(ClassRef)~ it || fastcast!(IntfRef)~ it);
  string pname;
  t2.gotIdentifier(pname);
  if (!t2.accept(")"[]))
    t2.failparse("closing paren expected"[]);
  IType hdltype = fastcast!(IType) (sysmod.lookup("_Handler"[])), objtype = fastcast!(ClassRef) (sysmod.lookup("Object"[]));
  string hdlmarker = Format("__hdlmarker_var_special_"[], getuid());
  assert(!namespace().lookup(hdlmarker));
  auto hdlvar = fastalloc!(Variable)(hdltype, framelength(), hdlmarker);
  auto csc = fastcast!(Scope)~ namespace();
  assert(!!csc);
  auto hdlst = fastalloc!(VarDecl)(hdlvar);
  hdlst.initInit;
  csc.addStatement(hdlst);
  csc.add(hdlvar);
  auto nf = fastalloc!(NestedFunction)(csc), mod = fastcast!(Module) (current_module());
  New(nf.type);
  nf.type.ret = Single!(Void);
  nf.type.params ~= Argument(objtype, "_obj"[]);
  static int hdlId;
  synchronized
    nf.name = Format("hdlfn_"[], hdlId++);
  nf.sup = mod;
  mod.addEntry(fastcast!(Tree) (nf));
  {
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(nf);
    nf.fixup;
    
    auto sc = new Scope;
    sc.configPosition(text);
    nf.addStatement(sc);
    namespace.set(sc);
    
    auto objvar = fastalloc!(Variable)(it, framelength(), cast(string) null);
    sc.addStatement(fastalloc!(VarDecl)(objvar, reinterpret_cast(it, fastcast!(Expr)~ nf.lookup("_obj"[], true))));
    sc.add(objvar);
    {
      auto ea = fastalloc!(ExprAlias)(objvar, pname);
      sc.add(ea);
    }
    auto nf2 = fastalloc!(NestedFunction)(sc);
    with (nf2) {
      New(type);
      type.ret = Single!(Void);
      type.params ~= Argument(Single!(Array, Single!(Char)), "n"[]);
      type.params ~= Argument(fastcast!(IType) (sysmod.lookup("Object"[])), "obj"[], fastcast!(Expr) (sysmod.lookup("null"[])));
      auto backup2 = namespace();
      scope(exit) namespace.set(backup2);
      sup = backup2;
      namespace.set(nf2);
      fixup;
      
      name = "invoke-exit";
      nf2.addStatement(iparse!(Statement, "cond_nest"[], "tree.stmt"[]) // can't use hdlvar here, because it's in the wrong scope
                        (`{
                            auto cm = _lookupCM(n, &hdlvar, true);
                            if (!cm.accepts(obj))
                              raise new Error "Couldn't invoke $n: bad argument: $(obj?.toString():`"`"`null`"`"`)";
                            handler-argument-variable = obj;
                            cm.jump();
                          }`, namespace(), "hdlvar"[], lookup(hdlmarker)));
      hdlvar.name = null; // marker string not needed
    }
    mod.addEntry(fastcast!(Tree) (nf2));
    sc.add(nf2);
    
    Scope sc2;
    if (!rest(t2, "tree.scope"[], &sc2))
      t2.failparse("No statement matched in handler context"[]);
    sc.addStatement(sc2);
  }
  {
    auto setup_st =
      iparse!(Statement, "var_setup_1"[], "tree.stmt"[])
             (`
             {
               var.id = class-id type;
               var.prev = __hdl__;
               var.dg = &fn;
               var.delimit = _cm;
               __hdl__ = &var;
             }`,
             namespace(), "var"[], hdlvar, "type"[], it, "fn"[], nf);
    assert(!!setup_st);
    csc.addStatement(setup_st);
  }
  {
    auto guard_st =
      iparse!(Statement, "hdl_undo"[], "tree.stmt"[])
              (`onSuccess __hdl__ = __hdl__.prev; `, csc);
    assert(!!guard_st);
    // again, no need to add (is NoOp)
  }
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotHdlStmt, "tree.stmt.hdl"[], "18"[], "set-handler"[]);

import ast.ifstmt;
Object gotExitStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  Expr ex;
  bool isString(IType it) { return test(Single!(Array, Single!(Char)) == it); }
  if (!rest(t2, "tree.expr"[], &ex) || !gotImplicitCast(ex, &isString))
    assert(false);
  IType cmtype = fastcast!(IType)~ sysmod.lookup("_CondMarker"[]);
  auto cmvar = fastalloc!(Variable)(cmtype, framelength(), cast(string) null);
  
  IType argType; string argName;
  if (t2.accept("("[])) {
    if (!rest(t2, "type"[], &argType))
      t2.failparse("Exit parameter type expected"[]);
    auto cr = fastcast!(ClassRef) (argType), ir = fastcast!(IntfRef) (argType);
    if (!cr && !ir)
      t2.failparse("Class or intf type expected"[]);
    
    t2.gotIdentifier(argName);
    if (!t2.accept(")"[]))
      t2.failparse("Closing parenthesis for exit parameter expected"[]);
  }
  
  auto csc = fastcast!(Scope)~ namespace();
  assert(!!csc);
  auto cmdecl = fastalloc!(VarDecl)(cmvar);
  cmdecl.initInit;
  csc.addStatement(cmdecl);
  csc.add(cmvar);
  {
    auto setup_st =
      iparse!(Statement, "hdl_setup"[], "tree.stmt"[])
             (`
             {
               var.prev = _cm;
               var.name = nex;
               if (_record) var.guard_id = _record.dg;
               // printf("unroll up to %p\n", _record);
               var.old_hdl = __hdl__;
               static if (type-is class atype) {
                var.param_id = class-id atype;
              }
               var.threadlocal = _threadlocal; // for win32
               _cm = &var;
             }`,
             namespace(), "var"[], cmvar, "nex"[], ex, "atype"[], argType?argType:voidp);
    assert(!!setup_st);
    csc.addStatement(setup_st);
  }
  {
    auto guard_st =
      iparse!(Statement, "cm_undo"[], "tree.stmt"[])
             (`onSuccess _cm = (_CondMarker*:_cm).prev; `, csc);
    assert(!!guard_st);
  }
  auto ifs = new IfStatement;
  ifs.wrapper = new Scope;
  ifs.test = iparse!(Cond, "cm_cond"[], "cond"[])
                    (`setjmp &(var.target)`,
                     "var"[], cmvar);
  assert(!!ifs.test);
  configure(ifs.test);
  auto sc = new Scope;
  
  auto nsbackup = namespace();
  scope(exit) namespace.set(nsbackup);
  namespace.set(sc);
  
  sc.addStatement(iparse!(Statement, "reset_threadlocal"[], "tree.stmt"[])
                         (`_threadlocal = var.threadlocal;`,
                          namespace(), "var"[], cmvar));
  if (argType) {
    auto var = fastalloc!(Variable)(argType, framelength(), argName);
    auto vd = fastalloc!(VarDecl)(var);
    sc.add(var);
    sc.addStatement(vd);
    sc.addStatement(iparse
      !(Statement, "cm_cast"[], "tree.scope"[])
        (`{
            var = at: handler-argument-variable;
            if !var raise new Error "Bad parameter type for exit: expected $(string-of at), got $(handler-argument-variable?.toString():\"(null)\")";
          }`, sc, "var"[], var, "at"[], argType)
    );
  }
  if (!t2.accept(";"[])) {
    Scope sc2;
    if (!rest(t2, "tree.scope"[], &sc2))
      t2.failparse("Couldn't get cond_exit branch"[]);
    sc.addStatement(sc2);
  }
  ifs.branch1 = sc;
  
  text = t2;
  return ifs;
}
mixin DefaultParser!(gotExitStmt, "tree.stmt.cond_exit"[], "181"[], "define-exit"[]);
