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

Expr lookupOp(string op, bool allowNone, Expr[] exprs...) {
  bool reassign;
  auto pre = op.endsWith("=");
  if (pre && op[0] != '=' /or/ '!') {
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
    if (allowNone) return null;
    logln("No matching operators (", op, ") defined for ", exprs /map/ ex!("e -> e.valueType()"), ", exs being ", exprs);
    asm { int 3; }
  } else
    throw new Exception(Format("No such operator defined: ", op, " (tried for ", exprs /map/ ex!("e -> e.valueType()"), ")"));
}

Expr lookupOp(string op, Expr[] exprs...) {
  return lookupOp(op, false, exprs);
}
