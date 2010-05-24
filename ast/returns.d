module ast.returns;

import ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse;

class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  override void emitAsm(AsmFile af) {
    auto fun = ns.get!(Function);
    assert(value.valueType().size == 4);
    value.emitAsm(af);
    af.mmove4("(%esp)", "%eax");
    // TODO: stack cleanup token here
    af.put("jmp ", fun._scope.exit());
  }
}

Object gotRetStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("return ")) {
    auto rs = new ReturnStmt;
    rs.ns = namespace();
    if (rest(t2, "tree.expr", &rs.value)) {
      text = t2;
      return rs;
    } else throw new Exception("Error parsing return expression at "~t2.next_text());
  } else return null;
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return");
