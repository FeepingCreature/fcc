module ast.globvars;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.pointer;

class GlobVar : LValue, Named {
  IType type;
  string name;
  bool tls;
  Namespace ns;
  mixin defaultIterate!();
  Expr initval;
  GlobVar dup() { assert(false, "hey stop it"); }
  string getInit() {
    if (!initval) return null;
    auto l = cast(Literal) initval;
    assert(!!l, Format(initval, " is not constant! "));
    return l.getValue();
  }
  this(IType t, string n, Namespace ns, bool tls, Expr initval) {
    this.type = t;
    this.name = n;
    this.ns = ns;
    this.tls = tls;
    this.initval = initval;
  }
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
    string toString() { return Format("global ", name, " of ", type); }
  }
}

class GlobVarDecl : Statement {
  GlobVar[] vars;
  bool tls;
  mixin defaultIterate!();
  override typeof(this) dup() { assert(false, "hey now.."); }
  override string toString() { return Format("declare ", tls?"tls ":"", vars); }
  override void emitAsm(AsmFile af) {
    if (tls) {
      foreach (var; vars)
        with (var) af.addTLS(mangled(), type.size, getInit());
    } else {
      foreach (var; vars)
        af.globvars[var.mangled()] = stuple(var.type.size, var.getInit());
    }
  }
}

import ast.casting;
Object gotGlobVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  string name;
  auto t2 = text;
  if (!rest(t2, "type", &ty)) return null;
  auto gvd = new GlobVarDecl;
  gvd.tls = true;
  auto ns = namespace();
  string t3; Expr initval;
  if (
    !t2.bjoin(
      t2.gotIdentifier(name) &&
      (
        (
          t3 = t2, t3.accept(" = ")
          && rest(t3, "tree.expr", &initval) && gotImplicitCast(initval, (Expr ex) {
            return ex.valueType() == ty
                   && !! cast(Literal) ex;
          })
          && (t2 = t3, true)
        ) || true
      ),
      t2.accept(","),
      {
        gvd.vars ~= new GlobVar(ty, name, ns, gvd.tls, initval);
        initval = null;
      },
      false
    )
    || !t2.accept(";")
  )
    return null;
  
  foreach (var; gvd.vars)
    ns.add(var.name, var);
  text = t2;
  return gvd;
}
mixin DefaultParser!(gotGlobVarDecl, "tree.toplevel.globvar");
