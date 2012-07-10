module ast.aggregate_parse;

import ast.aggregate, ast.parse, ast.base, ast.scopes, ast.namespace, ast.fun, ast.modules;

AggrStatement parseAggregateBody(ref string text, ParseCb rest, bool error = false, Statement* outp = null) {
  auto t2 = text;
  auto as = new AggrStatement;
  if (outp) *outp = as;
  Statement st;
  if (t2.many(!!rest(t2, "tree.stmt"[], &st), { as.stmts ~= st; }, "}")) {
    text = t2;
    return as;
  }
  else {
    if (error) t2.failparse("Could not parse statement");
    return null;
  }
}

AggrStatement parseFullAggregateBody(ref string src, ParseCb rest) {
  auto res = parseAggregateBody(src, rest, true);
  src = src.mystripl();
  if (src.length) {
    src.failparse("unknown text in aggregate body");
  }
  return res;
}

Object gotAggregateStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = new Scope;
  sc.configPosition(t2);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  if (auto as = t2.parseAggregateBody(rest, false, &sc._body)) {
    string tryId;
    if (!t2.accept("}")) {
      auto t3 = t2;
      if (t2.gotIdentifier(tryId)) {
        if (auto hint = locate_name(tryId)) {
          t3.failparse("unknown statement: identifier '", tryId, "' appears in ", hint);
        }
      }
      t3.failparse("unknown statement");
    }
    sc._body = as;
    text = t2;
    return sc;
  }
  else return null;
}
mixin DefaultParser!(gotAggregateStmt, "tree.stmt.aggregate"[], "131"[], "{"[]);

Object gotRestStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = new Scope;
  sc.configPosition(t2);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto as = new AggrStatement;
  sc.addStatement(as);
  Statement st;
  t2.many(!!rest(t2, "tree.stmt"[], &st), { as.stmts ~= st; });
  auto t3 = t2;
  if (t3.mystripl().length)
    t3.mustAccept("}"[], "Unterminated rest statement: "[]);
  text = t2;
  return sc;
}
mixin DefaultParser!(gotRestStmt, "tree.stmt.aggregate.rest"[], "132"[], "::"[]);
