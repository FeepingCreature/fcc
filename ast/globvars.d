module ast.globvars;

import ast.base, ast.parse, ast.modules, ast.namespace;

class GlobVar : LValue, Named {
  IType type;
  string name;
  Module mod;
  mixin defaultIterate!();
  this(IType t, string n, Module mod) { this.type = t; this.name = n; this.mod = mod; }
  string mangled() {
    return "global_"~mod.mangle(name, type);
  }
  override {
    IType valueType() { return type; }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      af.pushStack(mangled(), type);
    }
    void emitLocation(AsmFile af) {
      af.pushStack("$"~mangled(), type);
    }
  }
  string toString() { return Format("global ", type, " ", name); }
}

class GlobVarDecl : Statement {
  GlobVar[] vars;
  mixin defaultIterate!();
  override void emitAsm(AsmFile af) {
    foreach (var; vars)
      af.globvars[var.mangled()] = var.type.size;
  }
}

import tools.log;
Object gotGlobVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  string name;
  auto t2 = text;
  if (!rest(t2, "type", &ty)) return null;
  auto gvd = new GlobVarDecl;
  auto mod = namespace().get!(Module);
  if (!t2.bjoin(t2.gotIdentifier(name), t2.accept(","), {
    gvd.vars ~= new GlobVar(ty, name, mod);
  }, false) || !t2.accept(";"))
    return null;
  
  foreach (var; gvd.vars)
    mod.add(name, var);
  text = t2;
  return gvd;
}
mixin DefaultParser!(gotGlobVarDecl, "tree.toplevel.globvar");
