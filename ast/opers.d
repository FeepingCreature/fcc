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

Expr lookupOp(string text, string op, bool allowNone, Expr[] exprs...) {
  bool reassign;
  auto pre = op.endsWith("=");
  LValue lv; MValue mv;
  if (pre && op[0] != '=' /or/ '!') {
    lv = fastcast!(LValue) (exprs[0]);
    mv = fastcast!(MValue) (exprs[0]);
    if (!lv && !mv) {
      throw new Exception(Format(
        "Cannot ", op, " since exprs[0]: ", exprs[0], " is not an lvalue or mvalue! "
      ));
    }
    reassign = true;
    op = pre;
  }
  if (auto p = op in operdb) {
    foreach (dg; *p)
      if (auto res = dg(exprs)) {
        if (reassign) {
          if (lv) return new StatementAndExpr(new Assignment (lv, res), exprs[0]);
          else    return new StatementAndExpr(new AssignmentM(mv, res), exprs[0]);
        } else {
          return res;
        }
      }
    if (allowNone) return null;
    // asm { int 3; }
    throw new Exception(Format("No matching operators (", op, ") defined for ", exprs /map/ ex!("e -> e.valueType()"), ", exs being ", exprs));
  } else {
    throw new Exception(Format("No such operator defined: ", op, " (tried for ", exprs /map/ ex!("e -> e.valueType()"), ")"));
  }
}

Expr lookupOp(string op, bool allowNone, Expr[] exprs...) {
  return lookupOp(null, op, allowNone, exprs);
}

Expr lookupOp(string op, Expr[] exprs...) {
  return lookupOp(op, false, exprs);
}
