module ast.unary;

import ast.base, ast.math, ast.assign, ast.literals, parseBase;

class PostOpExpr(bool Inc) : Expr {
  LValue a; Assignment b;
  this(LValue a) {
    this.a = a;
    b = new Assignment(a, new AsmBinopExpr!(Inc?"addl":"subl")(a, new IntExpr(1)));
  }
  override {
    Type valueType() {
      return a.valueType();
    }
    void emitAsm(AsmFile af) {
      a.emitAsm(af);
      b.emitAsm(af);
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
    return new PostOpExpr!(true)(lv);
  } else if (t2.accept("--")) {
    auto lv = cast(LValue) op;
    if (!lv) throw new Exception(Format("Can't post-decrement ", op, ": not an lvalue"));
    text = t2;
    return new PostOpExpr!(false)(lv);
  } else return null;
}
mixin DefaultParser!(gotPostIncExpr, "tree.expr.arith.postinc", "25");
