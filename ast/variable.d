module ast.variable;

import ast.base, ast.math, ast.literals, parseBase, ast.casting, ast.static_arrays: DataExpr;

class Variable : LValue, Named {
  string address() { return Format(baseOffset, "(%ebp)"); }
  override {
    void emitAsm(AsmFile af) {
      af.pushStack(address, type);
    }
    void emitLocation(AsmFile af) {
      (new AsmBinopExpr!("addl")(new Register!("ebp"), new IntExpr(baseOffset))).emitAsm(af);
    }
    IType valueType() {
      return type;
    }
  }
  IType type;
  string name;
  // offset off ebp
  int baseOffset;
  Expr initval;
  void initInit() {
    if (initval) return;
    else initval = new ReinterpretCast!(Expr) (
      valueType(),
      new DataExpr(type.initval())
    );
  }
  this() { }
  this(IType t, string s, int i) {
    type = t;
    name = s;
    baseOffset = i;
    initInit();
  }
  override string getIdentifier() { return name; }
  mixin defaultIterate!(initval);
  string toString() { return Format("[ var ", name, " of ", type, " at ", baseOffset, "]"); }
}
