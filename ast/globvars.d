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
    if (!initval) return "zeroinitializer";
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
  void checkDecl(LLVMFile lf) {
    auto mang = mangleSelf();
    string sectioninfo;
    if (tls) sectioninfo = ", section \"tlsvars\"";
    if (once(lf, "symbol ", mang)) {
      lf.decls[mang] = qformat("@", mang, " = external global ", typeToLLVM(type), sectioninfo);
    }
  }
  override {
    string mangleSelf() {
      if (!manglecache)
        manglecache = qformat(tls?"tls_"[]:""[], "global_", ns.mangle(cleanedName(), type));
      return manglecache;
    }
    void markWeak() { weak = true; }
    void markExternC() { fail; }
    IType valueType() { return type; }
    string getIdentifier() { return cleanedName(); }
    void emitLLVM(LLVMFile lf) {
      emitLocation(lf);
      load(lf, "load ", typeToLLVM(type), "* ", lf.pop());
    }
    void emitLocation(LLVMFile lf) {
      checkDecl(lf);
      push(lf, "@", mangleSelf());
      if (tls) {
        string v = lf.pop();
        auto tlsinfo = fastcast!(Expr) (namespace().lookup(tlsbase));
        if (!tlsinfo) {
          logln("Cannot emit global variable ", name, ": no tls variable found under ", namespace());
          fail;
        }
        auto datastart = save(lf, fastalloc!(Symbol)("_sys_tls_data_start", Single!(Void)));
        datastart = save(lf, "ptrtoint i8* ", datastart, " to %size_t");
        
        tlsinfo.emitLLVM(lf);
        string tls = lf.pop();
        tls = save(lf, "ptrtoint i8* ", tls, " to %size_t");
        
        v = save(lf, "ptrtoint ", typeToLLVM(type), "* ", v, " to %size_t");
        v = save(lf, "sub %size_t ", v, ", ", datastart);
        v = save(lf, "add %size_t ", v, ", ", tls);
        v = save(lf, "inttoptr %size_t ", v, " to ", typeToLLVM(type), "*");
        push(lf, v);
      }
    }
    string toString() { return Format("global "[], ns.get!(Module)().name, "."[], name, " of "[], type); }
  }
}

class GlobVarDecl : Statement, IsMangled {
  GlobVar[] vars;
  mixin defaultIterate!();
  override {
    string mangleSelf() {
      return vars[0].mangleSelf();
    }
    void markWeak() {
      foreach (var; vars) var.markWeak();
    }
    void markExternC() {
      fail;
    }
    typeof(this) dup() {
      auto res = new GlobVarDecl;
      foreach (var; vars) {
        auto v2 = fastalloc!(GlobVar)(var.type, var.name, var.ns, var.tls, var.initval?var.initval.dup:null);
        v2.weak = var.weak;
        res.vars ~= v2;
      }
      return res;
    }
    string toString() { return Format("declare ", vars); }
    void emitLLVM(LLVMFile lf) {
      foreach (var; vars) /*if (var.type.llvmSize() != "0")*/ {
        string linkage;
        if (var.weak) linkage = "weak_odr ";
        string sectioninfo;
        if (var.tls) sectioninfo = ", section \"tlsvars\"";
        auto mangle = var.mangleSelf();
        string section = "module";
        if (var.tls) section = "tlsdefs";
        putSection(lf, section, "@", mangle, " = "~linkage~"global ", typeToLLVM(var.type), " ", var.getInit(), sectioninfo, ", align 16");
        lf.undecls[mangle] = true;
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
        gvd.vars ~= fastalloc!(GlobVar)(ty, name, ns, !shared, initval);
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
