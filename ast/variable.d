module ast.variable;

import ast.base, ast.opers, ast.literals, parseBase, ast.casting, ast.static_arrays: DataExpr;

import tools.log;
class Variable : LValue, Named {
  string address() { return Format(baseOffset, "(%ebp)"); }
  override {
    void emitAsm(AsmFile af) {
      if (type == Single!(Void)) return;
      mixin(mustOffset("type.size"));
      af.pushStack(address, type);
    }
    void emitLocation(AsmFile af) {
      lookupOp("+", new Register!("ebp"), mkInt(baseOffset)).emitAsm(af);
    }
    IType valueType() {
      return type;
    }
  }
  IType type;
  string name;
  // offset off ebp
  int baseOffset;
  bool dontInit;
  Expr initval;
  void initInit() {
    if (type == Single!(Void)) return;
    if (!type.initval.length)
      throw new Exception("Cannot declare an unsized variable: '"~name~"' being "~Format(type)~"! ");
    if (initval) return;
    else {
      initval = new ReinterpretCast!(Expr) (
        valueType(),
        new DataExpr(type.initval())
      );
    }
  }
  this() { }
  this(IType t, string s, int i) {
    type = t;
    name = s;
    baseOffset = i;
    initInit();
  }
  override string getIdentifier() { return name; }
  mixin DefaultDup!();
  mixin defaultIterate!(initval);
  string toString() {
    if (name) return name;
    return Format("[ var of ", type, " at ", baseOffset, initval?Format(" = ", initval):"", "]");
  }
}
