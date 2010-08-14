module ast.aggregate;

import ast.base, ast.parse;

class AggrStatement : Statement {
  Statement[] stmts;
  mixin defaultIterate!(stmts);
  override void emitAsm(AsmFile af) {
    foreach (stmt; stmts)
      stmt.emitAsm(af);
  }
  string toString() { return Format(stmts); }
}

import ast.scopes, ast.namespace, ast.fun;
Object gotAggregateStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("{")) return null;
  auto sc = new Scope;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto as = new AggrStatement;
  Statement st;
  if (t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; }, "}") &&
      t2.mustAccept("}", Format("Encountered unknown statement at ", t2.next_text()))
    ) { text = t2; sc._body = as; return sc; }
  else return null;
}
mixin DefaultParser!(gotAggregateStmt, "tree.stmt.aggregate");

Object gotRestStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("::")) return null;
  auto sc = new Scope;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto as = new AggrStatement;
  Statement st;
  t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; });
  auto t3 = t2;
  if (t3.strip().length) t3.mustAccept("}", "Unterminated rest statement: "~t3.next_text());
  text = t2;
  sc._body = as;
  return sc;
}
mixin DefaultParser!(gotRestStmt, "tree.stmt.aggregate.rest");
