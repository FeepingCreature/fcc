module ast.globvars;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.pointer;

class GlobVar : LValue, Named {
  IType type;
  string name;
  bool tls;
  Namespace ns;
  mixin defaultIterate!();
  Expr initval;
  GlobVar dup() { return this; /* invariant */ }
  string getInit() {
    if (!initval) return null;
    auto l = fastcast!(Literal) (initval);
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
  string cleanedName() {
    return name.replace("-", "_dash_");
  }
  string mangled() {
    return (tls?"tls_":"")~"global_"~ns.mangle(cleanedName(), type);
  }
  override {
    IType valueType() { return type; }
    string getIdentifier() { return cleanedName(); }
    void emitAsm(AsmFile af) {
      if (tls) {
        af.mmove4(qformat("$", mangled()), "%eax");
        af.mathOp("subl", "$_sys_tls_data_start", "%eax");
        af.mathOp("addl", "%esi", "%eax");
        af.pushStack("(%eax)", type);
      }
      else
        af.pushStack(mangled(), type);
    }
    void emitLocation(AsmFile af) {
      if (tls) {
        af.mmove4(qformat("$", mangled()), "%eax");
        af.mathOp("subl", "$_sys_tls_data_start", "%eax");
        af.mathOp("addl", "%esi", "%eax");
        af.pushStack("%eax", voidp);
        af.nvm("%eax");
      } else {
        af.pushStack(qformat("$", mangled()), voidp);
      }
    }
    string toString() { return Format("global ", name, " of ", type); }
  }
}

class GlobVarDecl : Statement, IsMangled {
  GlobVar[] vars;
  bool tls;
  mixin defaultIterate!();
  override {
    string mangleSelf() {
      return vars[0].mangled();
    }
    void markWeak() {
      // logln("weak globvar?! ", this);
      // ^ wat
    }
    typeof(this) dup() {
      auto res = new GlobVarDecl;
      foreach (var; vars) {
        auto v2 = new GlobVar(var.type, var.name, var.ns, var.tls, var.initval?var.initval.dup:null);
        res.vars ~= v2;
      }
      res.tls = tls;
      return res;
    }
    string toString() { return Format("declare ", tls?"tls ":"", vars); }
    void emitAsm(AsmFile af) {
      if (tls) {
        foreach (var; vars)
          with (var) if (type.size)
            af.addTLS(mangled(), type.size, getInit());
      } else {
        foreach (var; vars)
          with (var) if (type.size)
            af.globvars[mangled()] = stuple(type.size, getInit());
      }
    }
  }
}

import ast.casting, ast.fold;
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
          t3 = t2, t3.accept("=")
          && rest(t3, "tree.expr", &initval) && gotImplicitCast(initval, (Expr ex) {
            return ex.valueType() == ty
                   && !! fastcast!(Literal) (fold(ex));
          })
          && (t2 = t3, true)
        ) || true
      ),
      t2.accept(","),
      {
        gvd.vars ~= new GlobVar(ty, name, ns, gvd.tls, foldex(initval));
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
