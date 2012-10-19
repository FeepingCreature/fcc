module ast.prefixfun;

import ast.fun, ast.base, ast.namespace, ast.tuples, ast.structure;

// basically this code is massively unstable and probably a wellspring of bugs
// but it works for now.
// if it breaks, put the blame squarely on me. fair?
class PrefixFunction : Function {
  Expr prefix;
  Function supfun;
  void delegate(Argument[]) fixupDefaultArgs;
  this(Expr prefix, Function sup, void delegate(Argument[]) fda = null) {
    this.prefix = prefix;
    this.type = sup.type;
    this.name = "[wrap]"~sup.name;
    this.sup = sup.sup;
    this.supfun = sup;
    this.reassign = sup.reassign;
    this.fixupDefaultArgs = fda;
    // assert(sup.extern_c);
    // TODO: this may later cause problems
    extern_c = true; // sooorta.
  }
  private this() { }
  Argument[] fixupArgs(Argument[] arg) {
    if (fixupDefaultArgs) fixupDefaultArgs(arg);
    return arg;
  }
  override {
    // haax
    // Expr getPointer() { logln("Can't get pointer to prefix-extended function! "[]); assert(false); }
    Expr getPointer() { return supfun.getPointer(); }
    string toString() { return Format("prefix "[], prefix, " to "[], super.toString()); }
    Argument[] getParams(bool implicits) {
      if (implicits) return supfun.getParams(true);
      
      auto res = supfun.getParams(false);
      if (res.length > 1) return fixupArgs(res[1..$]);
      
      auto tup = fastcast!(Tuple) (res[0].type);
      if (!tup) { return null; }
      
      auto restypes = tup.types[1 .. $];
      Argument[] resargs;
      foreach (type; restypes) resargs ~= Argument(type);
      return fixupArgs(resargs);
    }
    PrefixFunction alloc() { return new PrefixFunction; }
    void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
      if (mode == IterMode.Semantic) {
        defaultIterate!(prefix).iterate(dg);
        supfun.iterate(dg, mode);
      }
      super.iterate(dg, mode);
    }
    PrefixFunction flatdup() {
      PrefixFunction res = cast(PrefixFunction) cast(void*) super.flatdup();
      res.prefix = prefix.dup;
      res.supfun = supfun;
      res.sup = sup;
      res.fixupDefaultArgs = fixupDefaultArgs;
      return res;
    }
    PrefixFunction dup() {
      auto res = flatdup();
      res.supfun = supfun.dup;
      return res;
    }
    PrefixCall mkCall() { return fastalloc!(PrefixCall)(this, prefix, supfun.mkCall()); }
    int fixup() { assert(false); } // this better be extern(C)
    string exit() { assert(false); }
    void emitLLVM(LLVMFile lf) { assert(false); }
    Stuple!(IType, string)[] stackframe() { assert(false); }
    Object lookup(string name, bool local = false) { assert(false); }
  }
}

class PrefixCall : FunCall {
  Expr prefix;
  FunCall sup;
  this(Function fun, Expr prefix, FunCall sup) {
    this.fun = fun;
    this.prefix = prefix;
    this.sup = sup;
  }
  Expr[] getParams() { return sup.getParams() ~ prefix ~ super.getParams(); }
  private this() { }
  PrefixCall dup() {
    auto res = fastalloc!(PrefixCall)(fun.flatdup, prefix.dup, sup.dup);
    foreach (param; params) res.params ~= param.dup;
    return res;
  }
  override void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    defaultIterate!(prefix).iterate(dg, mode);
    sup.iterate(dg, mode);
    super.iterate(dg, mode);
  }
  override void emitWithArgs(LLVMFile lf, Expr[] args) {
    auto res = fun.getParams(true);
    // Argument[] tlsptr;
    if (res.length && res[$-1].name == tlsbase) {
      // tlsptr = res[$-1..$];
      res = res[0..$-1];
    }
    if (res.length > 1) { sup.emitWithArgs(lf, prefix~args); return; }
    
    if (!res.length) fail;
    auto tup = fastcast!(Tuple) (res[0].type);
    if (!tup) { sup.emitWithArgs(lf, prefix~args); return; }
    auto nargs = new Expr[1];
    nargs[0] = mkTupleExpr(prefix~args);
    sup.emitWithArgs(lf, nargs);
  }
  override string toString() { return Format("prefixcall("[], fun, " [prefix] "[], prefix, " [rest] "[], sup, ": "[], super.getParams(), ")"[]); }
  override IType valueType() { return sup.valueType(); }
}

// only add those functions from ext2 that are not like any already in ext
Extensible extend_masked(Extensible ext, Extensible ext2) {
  auto os = fastcast!(OverloadSet) (ext);
  if (!os) return ext;
  Function[] newfuns;
  if (auto os2 = fastcast!(OverloadSet) (ext2)) newfuns = os2.funs;
  else if (auto fun2 = fastcast!(Function) (ext2)) newfuns ~= fun2;
  outer:foreach (newfun; newfuns) {
    foreach (fun; os.funs) {
      if (fun.type == newfun.type) continue outer; // mask
    }
    os = fastcast!(OverloadSet) (os.extend(newfun));
  }
  return os;
}
