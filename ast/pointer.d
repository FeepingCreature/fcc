module ast.pointer;

import ast.types, ast.base, parseBase, tools.base: This, This_fn, rmSpace, Ret, Params;

import dwarf2;
class Pointer_ : Type, Dwarf2Encodable {
  IType target;
  this(IType t) { target = forcedConvert(t); if (!target) asm { int 3; } }
  IType proxycache;
  string targettypecmp, lltypecache;
  bool proxying;
  IType _proxyType() {
    if (proxying) return null; // loop breaker, ie. as_type x x*
    proxying = true; scope(exit) proxying = false;
    if (auto tp = target.proxyType()) return fastalloc!(Pointer)(tp);
    return null;
  }
  override {
    mixin memoize!(_proxyType, proxycache, "proxyType");
    int opEquals(IType ty) {
      ty = resolveType(ty);
      if (!super.opEquals(ty)) return false;
      auto p = fastcast!(Pointer)~ ty;
      return target is p.target || target == p.target;
    }
    string llvmSize() { if (nativePtrSize == 4) return "4"; if (nativePtrSize == 8) return "8"; assert(false); }
    // string llvmType() { return typeToLLVM(target) ~ "*"; }
    string llvmType() {
      auto tt = typeToLLVM(target);
      if (targettypecmp != tt) {
        targettypecmp = tt;
        lltypecache = qformat(tt, "*");
      }
      return lltypecache;
    }
    string mangle() { return qformat("ptrto_", target.mangle()); }
    string toString() { if (target is this) return "self*"; return Format(target, "*"[]); }
    bool canEncode() {
      auto d2e = fastcast!(Dwarf2Encodable)(resolveType(target));
      return d2e && d2e.canEncode();
    }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto targetref = registerType(dwarf2, fastcast!(Dwarf2Encodable) (resolveType(target)));
      auto targetpsec = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("pointer type"[]));
      with (targetpsec) {
        data ~= targetref;
        data ~= ".int\t4\t/* pointer size */";
      }
      return targetpsec;
    }
  }
}

final class Pointer : Pointer_ {
  static const isFinal = true;
  this(IType t) { super(t); }
}

alias Single!(Pointer, Single!(Void)) voidp;

// &foo
class RefExpr_ : Expr {
  CValue src;
  int counter;
  static int pointer_counter;
  this(CValue cv) { if (!cv) fail; this.src = cv; this(); }
  private this() {
    counter = pointer_counter ++;
    // if (counter == 5101) fail;
  }
  mixin defaultIterate!(src);
  override RefExpr_ dup() { return fastalloc!(RefExpr)(src.dup); } // alloc RefExpr, not RefExpr_!
  Expr collapse() {
    if (auto de = fastcast!(DerefExpr) (.collapse(fastcast!(Expr)(src)))) {
      return de.src;
    }
    return this;
  }
  IType type_cache;
  override {
    IType valueType() {
      if (!type_cache) type_cache = fastalloc!(Pointer)(src.valueType());
      return type_cache;
    }
    void emitLLVM(LLVMFile lf) {
      src.emitLocation(lf);
    }
    string toString() {
      return Format("&"[], src);
    }
  }
}

final class RefExpr : RefExpr_ {
  static const isFinal = true;
  this(CValue cv) { super(cv); }
}

// *foo
class DerefExpr_ : LValue, HasInfo {
  Expr src;
  int count;
  static int de_count;
  this(Expr ex) {
    this();
    src = ex;
    if (!fastcast!(Pointer) (resolveType(src.valueType())))
      throw new Exception(Format("Can't dereference non-pointer: "[], src));
  }
  private this() { count = de_count ++; }
  mixin defaultIterate!(src);
  override DerefExpr_ dup() { return fastalloc!(DerefExpr)(src.dup); }
  Expr collapse() {
    // LOL, good luck working out when this is useful (and yes it is)
    if (auto re = fastcast!(RefExpr) (.collapse(src))) {
      return re.src;
    }
    return this;
  }
  mixin defaultCollapse!();
  override {
    string getInfo() { return Format("count: "[], count); }
    IType valueType() { return fastcast!(Pointer) (resolveType(src.valueType())).target; }
    void emitLLVM(LLVMFile lf) {
      auto ptrtype = typeToLLVM(src.valueType);
      // use addrspace(1) to preserve null accesses so they can crash properly
      auto usf = is_unsafe_fast(); // if this is true, don't use addrspace(1)
      if (!usf) {
        auto fixedtype = qformat(ptrtype[0..$-1], " addrspace(1)*");
        string addrspacecast = "bitcast ";
        if (llvmver() >= 34) addrspacecast = "addrspacecast ";
        auto c = save(lf, src);
             c = save(lf, addrspacecast, ptrtype, " ", c, " to ", fixedtype);
        load(lf, "load ", fixedtype, " ", c);
      } else {
        load(lf, "load ", typeToLLVM(src.valueType), " ", save(lf, src));
      }
    }
    void emitLocation(LLVMFile lf) {
      src.emitLLVM(lf);
    }
  }
  string toString() { return Format("*"[], src); }
}

final class DerefExpr : DerefExpr_ {
  static const isFinal = true;
  this(Expr ex) { super(ex); }
}

bool isVoidP(IType it) {
  if (!it) return false;
  auto p = fastcast!(Pointer)~ it;
  if (!p) return false;
  return !!fastcast!(Void) (resolveType(p.target));
}

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    if (text.accept("*"[])) { return fastalloc!(Pointer)(cur); }
    else return null;
  };
  // Pointers must NOT autocast to void* unless expected!
  implicits ~= delegate void(Expr ex, IType target, void delegate(Expr, int) consider) {
    if (!target) return;
    if (auto p = fastcast!(Pointer) (resolveType(ex.valueType()))) {
      if (!isVoidP(p) && isVoidP(target)) {
        /* This is something of a fallback.
           As such, give it a lower score. */
        consider(dcm(reinterpret_cast(voidp, ex)), 1);
      }
    }
    return;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isVoidP(ex.valueType()) && fastcast!(Pointer) (resolveType(expect))) {
      return reinterpret_cast(expect, ex);
    }
    return null;
  };
}

import ast.fold, ast.casting;
Object gotRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (text.startsWith("&")) return null;
  auto t2 = text;
  
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.bin"[], &ex)) {
    text.setError("Address operator found but nothing to take address matched"[]);
    return null;
  }
  
  if (!gotImplicitCast(ex, (Expr ex) {
    auto f = collapse(forcedConvert(ex));
    unrollSAE(f);
    return test(fastcast!(CValue)~ f);
  })) {
    text.setError("Can't take reference: expression does not seem to have an address"[]);
    return null;
  }
  
  text = t2;
  auto thing = collapse(forcedConvert(ex));
  Statement st;
  if (auto _st = unrollSAE(thing)) st = _st;
  auto cv = fastcast!(CValue) (thing);
  assert(!!cv);
  
  Expr res = fastalloc!(RefExpr)(cv);
  if (st) res = mkStatementAndExpr(st, res);
  return fastcast!(Object) (res);
}
mixin DefaultParser!(gotRefExpr, "tree.expr.ref"[], "21"[], "&"[]);

Object gotDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.bin"[], &ex))
    t2.failparse("Dereference operator found but no expression matched"[]);
  
  if (!gotImplicitCast(ex, (IType it) { return !!fastcast!(Pointer) (it); })) {
    return null;
  }
  text = t2;
  return fastalloc!(DerefExpr)(ex);
}
mixin DefaultParser!(gotDerefExpr, "tree.expr.deref"[], "22"[], "*"[]);

/*
      // emit declaration
      if (!tree && extern_c && name) {
        auto ret = typeToLLVM(type.ret);
        string pars;
        foreach (arg; type.params) {
          if (pars) pars ~= ", ";
          pars ~= typeToLLVM(arg.type);
        }
        putSection(lf, "module", "declare ", ret, " @", fmn, "(", pars, ")");
        return;
      }
*/

class Symbol : Expr {
  string _name;
  string getName() { return _name; }
  IType type;
  bool defineme;
  this(string name, IType type) {
    this._name = name;
    this.type = type; if (!this.type) fail;
  }
  Symbol dup() { return new Symbol(getName(), type); }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  IType typecache;
  override IType valueType() { if (!typecache) typecache = fastalloc!(Pointer)(type); return typecache; }
  override void emitLLVM(LLVMFile lf) {
    auto ts = typeToLLVM(type);
    if (ts == "void") { ts = "i8"; }
    if (once(lf, "symbol ", getName())) {
      lf.decls[getName()] = qformat("@", getName(), " = external global ", ts);
    }
    push(lf, "@", getName());
  }
}

// fill string at emit-time via dg
class LateSymbol : Expr {
  void delegate(LLVMFile) dg;
  string* name;
  IType type;
  this(IType type, void delegate(LLVMFile) dg, string* name) { this.type = type; this.dg = dg; this.name = name; }
  private this() { }
  LateSymbol dup() { return fastalloc!(LateSymbol)(type, dg, name); }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override IType valueType() { return type; }
  override string toString() { return qformat("(", type, ") ", *name); }
  override void emitLLVM(LLVMFile lf) {
    // if (!*name) dg(lf);
    dg(lf);
    if (!*name) {
      logln("wat");
      fail;
    }
    push(lf, "@", *name);
  }
}

class PointerIndexAccess : LValue {
  Pointer ptrtype;
  Expr ptr, index;
  this(Expr ptr, Expr index) {
    if (auto ptr = fastcast!(Pointer)(resolveType(ptr.valueType()))) {
      ptrtype = ptr;
    } else fail(qformat(ptr.valueType(), " not a pointer"));
    this.ptr = ptr;
    this.index = index;
  }
  mixin defaultIterate!(ptr, index);
  mixin defaultCollapse!(); // TODO if index is statically 0, optimize to *base?
  override {
    IType valueType() { return ptrtype.target; }
    PointerIndexAccess dup() { return fastalloc!(PointerIndexAccess)(ptr.dup, index.dup); }
    string toString() { return qformat("(", ptr, ")[", index, "]"); }
    void emitLocation(LLVMFile lf) {
      auto lp = save(lf, ptr), li = save(lf, index);
      load(lf, "getelementptr inbounds ", typeToLLVM(ptrtype), " ", lp, ", i32 ", li);
    }
    void emitLLVM(LLVMFile lf) {
      emitLocation(lf);
      load(lf, "load ", typeToLLVM(ptrtype), " ", lf.pop());
    }
  }
}
