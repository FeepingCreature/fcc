module ast.variable;

import ast.base;

class Variable : Expr {
  override void emitAsm(AsmFile af) {
    assert(type.size == 4);
    af.pushStack(Format(baseOffset, "(%ebp)"), type);
  }
  override Type valueType() {
    return type;
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
    assert(var.type.size == 4);
    if (var.initval) {
      var.initval.emitAsm(af);
    } else {
      af.salloc(4);
    }
  }
}
