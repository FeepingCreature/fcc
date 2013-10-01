module ast.unary;

import ast.base, ast.casting, ast.opers, ast.assign, ast.literals, parseBase;

// definitely not an lvalue
class PrePostOpExpr(bool Post, bool Inc) : Expr {
  Expr ex;
  this(Expr ex) {
    this.ex = ex;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(ex);
  mixin defaultCollapse!();
  override {
    IType valueType() { return ex.valueType(); }
    void emitLLVM(LLVMFile lf) {
      auto op = lookupOp(Inc?"+":"-"[], ex, mkInt(1));
      Expr cv;
      if (ex.valueType() == op.valueType()) cv = op;
      else {
        cv = tryConvert(op, ex.valueType());
        if (!cv) throw new Exception(Format("PrePostOpExpr("[], Inc?"+":"-", "[]) failed: cannot reconvert "[], op.valueType(), " to "[], ex.valueType()));
      }
      auto as = mkAssignment(ex, cv);
      static if (Post) {
        ex.emitLLVM(lf);
        as.emitLLVM(lf);
      } else {
        as.emitLLVM(lf);
        ex.emitLLVM(lf);
      }
    }
  }
}

Object gotPostIncExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  if (t2.accept("++"[])) {
    auto lv = fastcast!(LValue) (op);
    auto mv = fastcast!(MValue) (op);
    if (!lv && !mv) throw new Exception(Format("Can't post-increment "[], op, ": not an lvalue or mvalue"[]));
    text = t2;
    return new PrePostOpExpr!(true, true)(op);
  } else if (t2.accept("--"[])) {
    auto lv = fastcast!(LValue)~ op;
    auto mv = fastcast!(MValue) (op);
    if (!lv && !mv) throw new Exception(Format("Can't post-decrement "[], op, ": not an lvalue or mvalue"[]));
    text = t2;
    return new PrePostOpExpr!(true, false)(op);
  } else return null;
}
mixin DefaultParser!(gotPostIncExpr, "tree.expr.arith.postincdec"[], "25"[]);

Object gotPreIncExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  
  if (t2.accept("++"[])) {
    if (!cont(t2, &op))
      t2.failparse("Can't find expression for pre-inc"[]);
    auto lv = fastcast!(LValue) (op);
    auto mv = fastcast!(MValue) (op);
    if (!lv && !mv) text.failparse("Can't pre-increment "[], op, ": not an lvalue or mvalue"[]);
    text = t2;
    return new PrePostOpExpr!(false, true)(op);
  } else if (t2.accept("--"[])) {
    if (!cont(t2, &op))
      t2.failparse("Can't find expression for pre-inc"[]);
    auto lv = fastcast!(LValue) (op);
    auto mv = fastcast!(MValue)~ op;
    if (!lv && !mv) text.failparse("Can't pre-decrement "[], op, ": not an lvalue or mvalue"[]);
    text = t2;
    return new PrePostOpExpr!(false, false)(op);
  } else return null;
}
mixin DefaultParser!(gotPreIncExpr, "tree.expr.arith.preincdec"[], "26"[]);
