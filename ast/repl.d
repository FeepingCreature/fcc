// compiler integration for std.repl
module ast.repl;

import ast.base, parseBase;
import
  ast.oop, ast.namespace, ast.scopes, ast.variable, ast.fun,
  ast.modules, ast.literals, ast.vardecl, ast.pointer;

void captureContext(Scope sc, Variable repl) {
  Namespace cur = sc;
  while (!fastcast!(Function) (cur)) {
    foreach (pair; cur.field) {
      auto name = pair._0;
      auto thing = pair._1;
      if (auto var = fastcast!(Variable) (thing)) if (var.name) {
        auto mod = lookupMod("std.repl"[]);
        auto vt = resolveType(var.valueType());
        Object kind;
        IType wanted;
        void select(Object thing, IType w) {
          kind = thing; wanted = w;
        }
        if (Single!(SysInt) == vt) select(mod.lookup("IntValue"), Single!(SysInt));
        if (Single!(Float) == vt) select(mod.lookup("FloatValue"), Single!(Float));
        if (fastcast!(ClassRef) (vt)) select(
          mod.lookup("ObjectValue"),
          new Pointer(fastcast!(IType) (sysmod.lookup("Object")))
        );
        IType kind_type = fastcast!(IType) (kind);
        if (kind_type) {
          sc.addStatement(
            iparse!(Statement, "bind_var"[], "tree.semicol_stmt"[])
                  (`repl.add(name, new ClassType WantedType: &var)`,
                    "repl"[], repl, "name"[], mkString(var.name),
                    "ClassType"[], kind_type, "WantedType"[], wanted,
                    "var"[], var)
          );
        }
      }
    }
    cur = cur.sup;
  }
}

Object gotInvokeRepl(ref string text, ParseCb cont, ParseCb rest) {
  IType repltype;
  if (!rest(text, "type"[], &repltype)) text.failparse("REPL class type expected"[]);
  auto replclass = fastcast!(ClassRef) (resolveType(repltype));
  if (!replclass) text.failparse("REPL class type expected"[]);
  
  if (!text.accept("with"[])) text.failparse("'with' expected"[]);
  
  IType intftype;
  if (!rest(text, "type"[], &intftype)) text.failparse("REPL interface class type expected"[]);
  auto intfclass = fastcast!(ClassRef) (resolveType(intftype));
  if (!intfclass) text.failparse("REPL interface class type expected"[]);
  
  auto sc = new Scope;
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(sc);
  
  Variable mkVarFor(Expr ex) {
    auto ty = ex.valueType();
    auto var = fastalloc!(Variable)(ty, framelength(), cast(string) null);
    auto vd = fastalloc!(VarDecl)(var);
    vd.initval = ex;
    sc.addStatement(vd);
    sc.add(var);
    return var;
  }
  
  auto repl = mkVarFor(
    iparse!(Expr, "inst_repl"[], "tree.expr _tree.expr.bin"[])
           (`new repl new intf`,
            "repl"[], repltype, "intf"[], intftype));
  
  captureContext(sc, repl);
  sc.addStatement(
    iparse!(Statement, "start_repl"[], "tree.semicol_stmt"[])
           (`var.run()`,
            "var"[], repl)
  );
  
  return sc;
}
mixin DefaultParser!(gotInvokeRepl, "tree.semicol_stmt.invoke"[], "4"[], "invoke-repl"[]);
