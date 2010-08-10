module ast.globvars;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.pointer;

class GlobVar : LValue, Named {
  IType type;
  string name;
  bool tls;
  Namespace ns;
  mixin defaultIterate!();
  this(IType t, string n, Namespace ns, bool tls) { this.type = t; this.name = n; this.ns = ns; this.tls = tls; }
  string mangled() {
    return (tls?"tls_":"")~"global_"~ns.mangle(name, type);
  }
  override {
    IType valueType() { return type; }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      if (tls) 
        af.pushStack("%gs:"~mangled()~"@NTPOFF", type);
      else
        af.pushStack(mangled(), type);
    }
    void emitLocation(AsmFile af) {
      if (tls) {
        af.pushStack("%gs:0", voidp);
        af.popStack("%eax", voidp);
        af.put("leal ", mangled()~"@NTPOFF(%eax), %eax");
        af.pushStack("%eax", voidp);
      } else {
        af.pushStack("$"~mangled(), voidp);
      }
    }
  }
  string toString() { return Format("global ", type, " ", name); }
}

class GlobVarDecl : Statement {
  GlobVar[] vars;
  bool tls;
  mixin defaultIterate!();
  override void emitAsm(AsmFile af) {
    if (tls) {
      foreach (var; vars)
        af.tlsvars[var.mangled()] = var.type.size;
    } else {
      foreach (var; vars)
        af.globvars[var.mangled()] = var.type.size;
    }
  }
}

import tools.log;
Object gotGlobVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  string name;
  auto t2 = text;
  if (!rest(t2, "type", &ty)) return null;
  auto gvd = new GlobVarDecl;
  gvd.tls = true;
  auto ns = namespace();
  if (!t2.bjoin(t2.gotIdentifier(name), t2.accept(","), {
    gvd.vars ~= new GlobVar(ty, name, ns, gvd.tls);
  }, false) || !t2.accept(";"))
    return null;
  
  foreach (var; gvd.vars)
    ns.add(name, var);
  text = t2;
  return gvd;
}
mixin DefaultParser!(gotGlobVarDecl, "tree.toplevel.globvar");
