module ast.casting;

import ast.base, ast.parse;

class ReinterpretCast(T) : T {
  T from; Type to;
  this(Type to, T from) { this.from = from; this.to = to; }
  override {
    Type valueType() { return to; }
    void emitAsm(AsmFile af) {
      from.emitAsm(af);
    }
    static if (is(typeof(from.emitLocation())))
      void emitLocation(AsmFile af) {
        from.emitLocation(af);
      }
  }
}
