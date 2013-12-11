module ast.aggregate_parse;

import ast.aggregate, ast.parse, ast.base, ast.scopes, ast.namespace, ast.fun, ast.modules;

Statement parseAggregateBody(ref string text, ParseCb rest, bool error = false, void delegate(Statement) outdg = null) {
  auto t2 = text;
  AggrStatement as;
  // I think this has to be here so that even the first statement is already added to the scope. TODO confirm.
  Statement st;
  if (t2.many(!!rest(t2, "tree.stmt"[], &st), { if (outdg) outdg(st); else as.stmts ~= st; }, "}")) {
    text = t2;
    if (outdg) return Single!(NoOp);
    else return as;
  }
  else {
    if (error) t2.failparse("Could not parse statement");
    return null;
  }
}

Statement parseFullAggregateBody(ref string src, ParseCb rest) {
  auto sc = namespace().get!(Scope);
  parseAggregateBody(src, rest, true, &sc.addStatement);
  src.eatComments();
  src = src.mystripl();
  if (src.length) {
    src.failparse("unknown text in aggregate body");
  }
  return Single!(NoOp);
}

Object gotAggregateStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = fastalloc!(Scope)();
  sc.configPosition(text);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  if (auto as = t2.parseAggregateBody(rest, false, &sc.addStatement)) {
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
    text = t2;
    return sc;
  }
  else return null;
}
mixin DefaultParser!(gotAggregateStmt, "tree.stmt.aggregate"[], "131"[], "{"[]);

Object gotRestStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = new Scope;
  sc.configPosition(text);
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
