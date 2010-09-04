module ast.opers; // generalized operator handling

Expr delegate(Expr[])[][string] operdb;

Expr lookupOp(string op, Expr[] exprs...) {
  if (auto p = op in operdb) {
    foreach (dg; *p)
      if (auto res = dg(exprs))
        return res;
  } else
    throw new Exception("No such operator defined: "~op);
}
