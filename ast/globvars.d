module ast.globvars;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.pointer;

class GlobVar : LValue, Named, IsMangled {
  IType type;
  string name;
  bool tls;
  Namespace ns;
  mixin defaultIterate!();
  Expr initval;
  bool weak;
  GlobVar dup() { return this; /* invariant */ }
  string getInit() {
    if (!initval) return null;
    auto l = fastcast!(Literal) (initval);
    assert(!!l, Format(initval, " is not constant! "[]));
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
    return name.replace("-"[], "_dash_"[]);
  }
  string manglecache;
  override {
    string mangleSelf() {
      if (!manglecache)
        manglecache = qformat(tls?"tls_"[]:""[], "global_", ns.mangle(cleanedName(), type));
      return manglecache;
    }
    void markWeak() { weak = true; }
    IType valueType() { return type; }
    string getIdentifier() { return cleanedName(); }
    void emitAsm(AsmFile af) {
      if (!type.size) return; // hah
      if (isARM) {
        af.mmove4(qformat("="[], mangleSelf()), "r2"[]);
        if (tls) {
          af.mmove4("=_sys_tls_data_start"[], "r3"[]);
          af.mathOp("sub"[], "r2"[], "r2"[], "r3"[]);
          af.mathOp("add"[], "r2"[], "r2"[], "r4"[]);
        }
        armpush(af, "r2"[], type.size);
        return;
      }
      if (tls) {
        af.mmove4(qformat("$"[], mangleSelf()), "%eax"[]);
        af.mathOp("subl"[], "$_sys_tls_data_start"[], "%eax"[]);
        af.mathOp("addl"[], "%esi"[], "%eax"[]);
        af.pushStack("(%eax)"[], type.size);
      }
      else {
        af.mmove4("$"~mangleSelf(), "%eax"[]);
        af.pushStack("(%eax)"[], type.size);
        // af.pushStack(mangleSelf(), type.size);
      }
    }
    void emitLocation(AsmFile af) {
      if (!type.size) {
        af.mmove4("$0"[], "%eax"[]); // lol
        af.pushStack("%eax"[], 4);
        return;
      }
      if (isARM) {
        af.mmove4(qformat("="[], mangleSelf()), "r2"[]);
        if (tls) {
          af.mmove4("=_sys_tls_data_start"[], "r3"[]);
          af.mathOp("sub"[], "r2"[], "r2"[], "r3"[]);
          af.mathOp("add"[], "r2"[], "r2"[], "r4"[]);
        }
        af.pushStack("r2"[], 4);
        return;
      }
      if (tls) {
        af.mmove4(qformat("$"[], mangleSelf()), "%eax"[]);
        af.mathOp("subl"[], "$_sys_tls_data_start"[], "%eax"[]);
        af.mathOp("addl"[], "%esi"[], "%eax"[]);
        af.pushStack("%eax"[], nativePtrSize);
        af.nvm("%eax"[]);
      } else {
        af.pushStack(qformat("$"[], mangleSelf()), nativePtrSize);
      }
    }
    string toString() { return Format("global "[], ns.get!(Module)().name, "."[], name, " of "[], type); }
  }
}

class GlobVarDecl : Statement, IsMangled {
  GlobVar[] vars;
  bool tls;
  mixin defaultIterate!();
  override {
    string mangleSelf() {
      return vars[0].mangleSelf();
    }
    void markWeak() {
      foreach (var; vars) var.markWeak();
    }
    typeof(this) dup() {
      auto res = new GlobVarDecl;
      foreach (var; vars) {
        auto v2 = fastalloc!(GlobVar)(var.type, var.name, var.ns, var.tls, var.initval?var.initval.dup:null);
        v2.weak = var.weak;
        res.vars ~= v2;
      }
      res.tls = tls;
      return res;
    }
    string toString() { return Format("declare "[], tls?"tls ":""[], vars); }
    void emitAsm(AsmFile af) {
      if (tls) {
        foreach (var; vars)
          with (var) if (type.size)
            af.addTLS(mangleSelf(), type.size, getInit(), var.weak);
      } else {
        foreach (var; vars)
          with (var) if (type.size)
            af.globvars[mangleSelf()] = stuple(type.size, getInit(), var.weak);
      }
    }
  }
}

import ast.casting, ast.fold;
Object gotGlobVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  string name;
  auto t2 = text;
  bool shared;
  if (t2.accept("shared"[])) shared = true;
  if (!rest(t2, "type"[], &ty)) return null;
  auto gvd = new GlobVarDecl;
  gvd.tls = !shared;
  auto ns = namespace();
  string t3; Expr initval;
  if (
    !t2.bjoin(
      t2.gotIdentifier(name) &&
      (
        (
          t3 = t2, t3.accept("="[])
          && rest(t3, "tree.expr"[], &initval) && gotImplicitCast(initval, (Expr ex) {
            return ex.valueType() == ty
                   && !! fastcast!(Literal) (fold(ex));
          })
          && (t2 = t3, true)
        ) || true
      ),
      t2.accept(","[]),
      {
        if (initval) opt(initval);
        gvd.vars ~= fastalloc!(GlobVar)(ty, name, ns, gvd.tls, initval);
        initval = null;
      },
      false
    )
    || !t2.accept(";"[])
  )
    return null;
  
  foreach (var; gvd.vars)
    ns.add(var.name, var);
  text = t2;
  return gvd;
}
mixin DefaultParser!(gotGlobVarDecl, "tree.toplevel.globvar"[]);
