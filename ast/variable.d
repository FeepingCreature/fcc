module ast.variable;

import ast.base, ast.math, ast.literals, parseBase;

class Variable : LValue {
  string address() { return Format(baseOffset, "(%ebp)"); }
  override {
    void emitAsm(AsmFile af) {
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

import ast.namespace, ast.scopes;
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text, var = new Variable;
  if (rest(t2, "type", &var.type) && t2.gotIdentifier(var.name)) {
    if (t2.accept("=")) {
      if (!rest(t2, "tree.expr", &var.initval))
        throw new Exception(Format("Couldn't read expression at ", t2.next_text()));
    }
    t2.mustAccept(";", Format("Missed trailing semicolon at ", t2.next_text()));
    var.baseOffset = -(cast(Scope) namespace()).framesize() - var.type.size;
    auto vd = new VarDecl;
    vd.var = var;
    namespace().add(var);
    text = t2;
    return vd;
  } else return null;
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl");
