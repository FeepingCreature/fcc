module ast.variable;

import ast.base, ast.math, ast.literals;

class Variable : LValue {
  string address() { return Format(baseOffset, "(%ebp)"); }
  override {
    void emitAsm(AsmFile af) {
      assert(type.size == 4);
      af.pushStack(address, type);
    }
    void emitLocation(AsmFile af) {
      (new AsmBinopExpr!("addl")(new Register!("ebp"), new IntExpr(baseOffset))).emitAsm(af);
    }
    Type valueType() {
      return type;
    }
  }
  Type type;
  string name;
  // offset off ebp
  int baseOffset;
  Expr initval;
  this(Type t, string s, int i) { type = t; name = s; baseOffset = i; }
  this() { }
  string toString() { return Format("[ var ", name, " of ", type, " at ", baseOffset, "]"); }
}

class VarDecl : Statement {
  Variable var;
  override void emitAsm(AsmFile af) {
    if (var.initval) {
      var.initval.emitAsm(af);
    } else {
      af.salloc(var.type.size);
    }
  }
}
