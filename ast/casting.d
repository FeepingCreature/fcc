module ast.casting;

import ast.base, ast.parse;

class ReinterpretCast(T) : T {
  T from; IType to;
  this(IType to, T from) { this.from = from; this.to = to; }
  mixin defaultIterate!(from);
  override {
    string toString() { return Format("reinterpret_cast<", to, "> ", from); }
    IType valueType() { return to; }
    void emitAsm(AsmFile af) {
      from.emitAsm(af);
    }
    static if (is(typeof(&from.emitLocation)))
      void emitLocation(AsmFile af) {
        from.emitLocation(af);
      }
  }
}

Object gotCastExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  IType dest;
  Expr ex;
  if (!(
    t2.accept("cast(") &&
    rest(t2, "type", &dest) &&
    t2.accept(")") &&
    rest(t2, "tree.expr", &ex)
  ))
    return null;
  text = t2;
  return new ReinterpretCast!(Expr)(dest, ex);
}
mixin DefaultParser!(gotCastExpr, "tree.expr.cast", "7");
