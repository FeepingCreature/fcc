module ast.aggregate;

import ast.base, ast.parse;

class AggrStatement : Statement {
  Statement[] stmts;
  mixin defaultIterate!(stmts);
  override void emitAsm(AsmFile af) {
    foreach (stmt; stmts)
      stmt.emitAsm(af);
  }
}

Object gotAggregateStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  AggrStatement as;
  Statement st;
  if (t2.accept("{") && (New(as), true) &&
      t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; }) &&
      t2.mustAccept("}", Format("Encountered unknown statement at ", t2.next_text()))
    ) { text = t2; return as; }
  else return null;
}
mixin DefaultParser!(gotAggregateStmt, "tree.stmt.aggregate");
