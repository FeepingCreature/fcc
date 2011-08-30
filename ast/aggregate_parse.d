module ast.aggregate_parse;

import ast.aggregate, ast.parse, ast.base, ast.scopes, ast.namespace, ast.fun;
Object gotAggregateStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = new Scope;
  sc.configPosition(t2);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto as = new AggrStatement;
  sc._body = as;
  Statement st;
  if (t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; }, "}") &&
      t2.mustAccept("}", "Encountered unknown statement")
    ) { text = t2; return sc; }
  else return null;
}
mixin DefaultParser!(gotAggregateStmt, "tree.stmt.aggregate", "131", "{");

Object gotRestStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = new Scope;
  sc.configPosition(t2);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto as = new AggrStatement;
  sc.addStatement(as);
  Statement st;
  t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; });
  auto t3 = t2;
  if (t3.mystripl().length)
    t3.mustAccept("}", "Unterminated rest statement: ");
  text = t2;
  return sc;
}
mixin DefaultParser!(gotRestStmt, "tree.stmt.aggregate.rest", "132", "::");
