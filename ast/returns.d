module ast.returns;

import ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse;

class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  mixin defaultIterate!(value);
  override void emitAsm(AsmFile af) {
    auto fun = ns.get!(Function);
    if (value) {
      assert(value.valueType().size == 4);
      value.emitAsm(af);
      af.popStack("%eax", value.valueType());
    }
    // TODO: stack cleanup token here
    af.put("jmp ", fun._scope.exit());
  }
}

Object gotRetStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("return")) {
    auto rs = new ReturnStmt;
    rs.ns = namespace();
    auto fun = namespace().get!(Function)();
    text = t2;
    if (fun.type.ret == Single!(Void))
      return rs; // don't expect a value.
    if (rest(text, "tree.expr", &rs.value)) {
      return rs;
    } else throw new Exception("Error parsing return expression at "~text.next_text());
  } else return null;
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return");
