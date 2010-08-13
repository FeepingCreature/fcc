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

Object gotAggregateStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  AggrStatement as;
  Statement st;
  if (t2.accept("{") && (New(as), true) &&
      t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; }, "}") &&
      t2.mustAccept("}", Format("Encountered unknown statement at ", t2.next_text()))
    ) { text = t2; return as; }
  else return null;
}
mixin DefaultParser!(gotAggregateStmt, "tree.stmt.aggregate");

Object gotRestStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("::")) return null;
  auto as = new AggrStatement;
  Statement st;
  t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; });
  auto t3 = t2;
  if (t3.strip().length) t3.mustAccept("}", "Unterminated rest statement: "~t3.next_text());
  text = t2;
  return as;
}
mixin DefaultParser!(gotRestStmt, "tree.stmt.rest_aggregate");
