module ast.conditionals;

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
