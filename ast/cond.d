// conditions
module ast.cond;

import ast.base, ast.parse, ast.namespace, ast.oop, ast.tuples, ast.literal_string;

static int i;
Expr genConvertClassExpr(Expr ex) {
  /+auto cl = new Class("__convert_"~Format(i++)~"_for_"~ex.valueType().mangle(), null);
  auto tuptype = cast(Tuple) ex.valueType();
  if (tuptype) cl.iparents = [iparse!(IntfRef, "gencce_1", "type")
                                     (`sys.ITupleValue`).myIntf].dup;
  else cl.iparents = [iparse!(IntfRef, "gencce_2", "type")
                             (`sys.IExprValue`).myIntf].dup;
  auto exprs = getAllImplicitCasts(ex), tupex = mkTupleValueExpr(exprs);
  cl.sup = namespace();
  {
    namespace.set(cl);
    scope(exit) namespace.set(cl.sup);
    new RelMember("tuple", tupex.valueType(), cl);
    auto fun = iparse!(Function, "gencce_fun", "struct_fundef")
                      (`sys.IExprValue take(string type, void* to) { }`);
    auto sc = cast(Scope) fun.tree;
    assert(sc);
    {
      namespace.set(sc);
      scope(exit) namespace.set(cl);
      sc.addStatement(
        iparse!(Statement, "gencce_stmt", "tree.stmt")
               (`if (type == typestring) { *cast(type*) { to = tuple[id]; return; }`, namespace(),
                "type", exprs[0].valueType(),
                "typestring", new StringExpr(exprs[0].valueType())));
      assert(false);
      /*void addSt(int id) {
        auto type = exprs[id].valueType();
      */
    }
  }+/
  return null;
}

import ast.namespace, ast.modules, ast.vardecl, ast.variable, ast.scopes, ast.nestfun, ast.casting;
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
  auto hdlvar = new Variable(hdltype, null, boffs(hdltype));
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
  // nf.type.params ~= stuple(it, pname);
  nf.type.params ~= stuple(objtype, "_obj");
  nf.fixup;
  nf.sup = mod;
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
               var.prev = _hdl;
               var.dg = &fn;
               _hdl = &var;
             }`,
             "var", hdlvar, "type", it, "fn", nf);
    assert(setup_st);
    csc.addStatement(setup_st);
  }
  {
    auto guard_st =
      iparse!(Statement, "hdl_undo", "tree.stmt")
              (`onSuccess _hdl = _hdl.prev; `, namespace());
    assert(guard_st);
    // again, no need to add (is NoOp)
  }
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotHdlStmt, "tree.stmt.hdl", "18");
