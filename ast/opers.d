module ast.opers; // generalized operator handling

import ast.base, ast.assign, tools.base;

Expr delegate(Expr[])[][string] operdb;

void defineOp(string op, Expr delegate(Expr[]) dg) {
  operdb[op] ~= dg;
}

void defineOp(string op, Expr delegate(Expr) dg) {
  defineOp(op, dg /apply/ delegate Expr(typeof(dg) dg, Expr[] list) { if (list.length != 1) return null; return dg(list[0]); });
}

void defineOp(string op, Expr delegate(Expr, Expr) dg) {
  defineOp(op, dg /apply/ delegate Expr(typeof(dg) dg, Expr[] list) { if (list.length != 2) return null; return dg(list[0], list[1]); });
}

void defineOp(string op, Expr delegate(Expr, Expr, Expr) dg) {
  defineOp(op, dg /apply/ delegate Expr(typeof(dg) dg, Expr[] list) { if (list.length != 3) return null; return dg(list[0], list[1], list[2]); });
}

Expr lookupOp(string op, Expr[] exprs...) {
  bool reassign;
  if (auto pre = op.endsWith("=")) {
    if (!cast(LValue) exprs[0]) {
      throw new Exception(Format(
        "Cannot ", op, " since exprs[0]: ", exprs[0], " is not an lvalue! "
      ));
    }
    reassign = true;
    op = pre;
  }
  if (auto p = op in operdb) {
    foreach (dg; *p)
      if (auto res = dg(exprs)) {
        if (reassign) {
          return new StatementAndExpr(
            new Assignment(cast(LValue) exprs[0], res), exprs[0]);
        } else {
          return res;
        }
      }
    throw new Exception(Format("No matching operators (", op, ") defined for ", exprs /map/ ex!("e -> e.valueType()"), ", exs being ", exprs));
  } else
    throw new Exception("No such operator defined: "~op);
}
