module ast.unary;

import ast.base, ast.math, ast.assign, ast.literals, parseBase;

class PrePostOpExpr(bool Post, bool Inc) : LValue {
  LValue a; Assignment b;
  this(LValue a) {
    this.a = a;
    b = new Assignment(a, new AsmBinopExpr!(Inc?"addl":"subl")(a, new IntExpr(1)));
  }
  override {
    Type valueType() {
      return a.valueType();
    }
    void emitLocation(AsmFile af) {
      a.emitLocation(af);
    }
    void emitAsm(AsmFile af) {
      static if (Post) {
        a.emitAsm(af);
        b.emitAsm(af);
      } else {
        b.emitAsm(af);
        a.emitAsm(af);
      }
    }
  }
}

Object gotPostIncExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  if (t2.accept("++")) {
    auto lv = cast(LValue) op;
    if (!lv) throw new Exception(Format("Can't post-increment ", op, ": not an lvalue"));
    text = t2;
    return new PrePostOpExpr!(true, true)(lv);
  } else if (t2.accept("--")) {
    auto lv = cast(LValue) op;
    if (!lv) throw new Exception(Format("Can't post-decrement ", op, ": not an lvalue"));
    text = t2;
    return new PrePostOpExpr!(true, false)(lv);
  } else return null;
}
mixin DefaultParser!(gotPostIncExpr, "tree.expr.arith.postincdec", "25");

Object gotPreIncExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  
  if (t2.accept("++")) {
    if (!cont(t2, &op))
      throw new Exception(Format("Can't find expression for pre-inc at '"~t2.next_text()~"'"));
    auto lv = cast(LValue) op;
    if (!lv) throw new Exception(Format("Can't post-increment ", op, ": not an lvalue"));
    text = t2;
    return new PrePostOpExpr!(false, true)(lv);
  } else if (t2.accept("--")) {
    if (!cont(t2, &op))
      throw new Exception(Format("Can't find expression for pre-inc at '"~t2.next_text()~"'"));
    auto lv = cast(LValue) op;
    if (!lv) throw new Exception(Format("Can't post-decrement ", op, ": not an lvalue"));
    text = t2;
    return new PrePostOpExpr!(false, false)(lv);
  } else return null;
}
mixin DefaultParser!(gotPreIncExpr, "tree.expr.arith.preincdec", "26");
