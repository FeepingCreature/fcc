module ast.vardecl;

import ast.assign, ast.base;
public import ast.variable;

class VarDecl : Statement {
  Variable var;
  override void emitAsm(AsmFile af) {
    af.salloc(var.type.size);
    (new Assignment(var, var.initval)).emitAsm(af);
  }
}

// base offset
int boffs(Type t) {
  return -(cast(Scope) namespace()).framesize() - t.size;
}

static int x;
void mkVar(AsmFile af, Type type, void delegate(Variable) dg) {
  auto var = new Variable(type, Format("__temp_var_", x++, "__"), boffs(type));
  auto vd = new VarDecl;
  vd.var = var;
  vd.emitAsm(af);
  dg(var);
}

import ast.namespace, ast.scopes;
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text, var = new Variable;
  if (rest(t2, "type", &var.type) && t2.gotIdentifier(var.name)) {
    if (t2.accept("=")) {
      if (!rest(t2, "tree.expr", &var.initval))
        throw new Exception(Format("Couldn't read expression at ", t2.next_text()));
    }
    var.initInit();
    t2.mustAccept(";", Format("Missed trailing semicolon at ", t2.next_text()));
    if (var.valueType() != var.initval.valueType()) {
      error = Format("Mismatching types in initializer: ", var, " <- ", var.initval.valueType());
      return null;
    }
    var.baseOffset = boffs(var.type);
    auto vd = new VarDecl;
    vd.var = var;
    namespace().add(var);
    text = t2;
    return vd;
  } else return null;
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl");
