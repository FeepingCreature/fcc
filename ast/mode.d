module ast.mode;

import ast.base;
import
  ast.namespace, ast.fun, ast.fold, ast.literal_string, ast.scopes,
  ast.casting, ast.pointer, ast.aliasing, ast.vardecl: lvize;

import tools.ctfe: ctReplace;

class Mode {
  string config;
  string argname;
  this(string c, string a) { config = c; argname = a; }
  ModeSpace translate(Expr ex, ParseCb rest) {
    auto res = new ModeSpace;
    string prefix, suffix;
    auto cfg = config;
    while (cfg.length) {
      if (cfg.accept("prefix")) {
        if (!cfg.gotIdentifier(prefix))
          cfg.failparse("couldn't get prefix");
        res.prefixes ~= prefix;
        continue;
      }
      
      if (cfg.accept("suffix")) {
        if (!cfg.gotIdentifier(suffix))
          cfg.failparse("couldn't get suffix");
        res.suffixes ~= suffix;
        continue;
      }
      
      {
        auto backup = namespace();
        scope(exit) namespace.set(backup);
        // add the arg
        auto mns = new MiniNamespace("mode_arg");
        with (mns) {
          sup = backup;
          internalMode = true;
          if (argname) add(argname, ex);
        }
        namespace.set(mns);
        
        if (cfg.accept("first-arg")) {
          if (!rest(cfg, "tree.expr", &res.firstParam))
            cfg.failparse("Couldn't match first-arg arg! ");
          continue;
        }
      }
      cfg.failparse("Couldn't parse mode string");
    }
    return res;
  }
}

// basically this code is massively unstable and probably a wellspring of bugs
// but it works for now.
// if it breaks, put the blame squarely on me. fair?
class PrefixFunction : Function {
  Expr prefix;
  Function supfun;
  this(Expr prefix, Function sup) {
    this.prefix = prefix;
    this.type = sup.type;
    this.name = "[wrap]"~sup.name;
    this.sup = sup.sup;
    this.supfun = sup;
    this.reassign = sup.reassign;
    // assert(sup.extern_c);
    // TODO: this may later cause problems
    extern_c = true; // sooorta.
  }
  private this() { }
  // this pains me.
  override {
    // This pains me more.
    // Expr getPointer() { logln("Can't get pointer to prefix-extended function! "); assert(false); }
    Expr getPointer() { return supfun.getPointer(); }
    string toString() { return Format("prefix ", prefix, " to ", super.toString()); }
    Argument[] getParams() {
      auto res = supfun.getParams();
      if (res.length > 1) return res[1..$];
      
      auto tup = fastcast!(Tuple) (res[0].type);
      if (!tup) { return null; }
      
      auto restypes = tup.types[1 .. $];
      Argument[] resargs;
      foreach (type; restypes) resargs ~= Argument(type);
      return resargs;
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
      return res;
    }
    PrefixFunction dup() {
      auto res = flatdup();
      res.supfun = supfun.dup;
      return res;
    }
    PrefixCall mkCall() { return new PrefixCall(this, prefix, supfun.mkCall()); }
    int fixup() { assert(false); } // this better be extern(C)
    string exit() { assert(false); }
    int framestart() { assert(false); }
    void emitAsm(AsmFile af) { assert(false); }
    Stuple!(IType, string, int)[] stackframe() { assert(false); }
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
  Expr[] getParams() { return prefix ~ sup.getParams() ~ super.getParams(); }
  private this() { }
  PrefixCall dup() {
    auto res = new PrefixCall;
    res.fun = fun.flatdup;
    res.prefix = prefix.dup;
    res.sup = sup.dup;
    return res;
  }
  override void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    defaultIterate!(prefix).iterate(dg, mode);
    sup.iterate(dg, mode);
  }
  override void emitWithArgs(AsmFile af, Expr[] args) {
    // logln("prefix call, prepend ", prefix);
    sup.emitWithArgs(af, prefix ~ args);
  }
  override string toString() { return Format("prefixcall(", fun, " [prefix] ", prefix, " [rest] ", sup, ")"); }
  override IType valueType() { return sup.valueType(); }
}

class ModeSpace : Namespace, ScopeLike {
  Expr firstParam;
  string[] prefixes, suffixes;
  bool substituteDashes;
  this() { sup = namespace(); }
  override {
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() { return sup.stackframe(); }
    int framesize() { return (fastcast!(ScopeLike)~ sup).framesize(); }
    mixin DefaultScopeLikeGuards!();
    Object lookup(string name, bool local = false) {
      Object funfilt(Object obj) {
        if (auto fun = fastcast!(Function)~ obj) {
          if (!firstParam) return fun;
          if (!fun.extern_c) return fun;
          if (!fun.type) return fun;
          auto params = fun.type.params;
          if (!params.length) return fun;
          auto firstType = params[0].type;
          Expr fp = firstParam;
          bool exactlyEqual(IType a, IType b) {
            auto pa = fastcast!(Pointer)~ a, pb = fastcast!(Pointer)~ b;
            if (pa && pb) return exactlyEqual(pa.target, pb.target);
            if (!pa && pb || pa && !pb) return false;
            IType resolveMyType(IType it) {
              if (fastcast!(TypeAlias) (it)) return it;
              if (auto tp = it.proxyType())
                return resolveMyType(tp);
              return it;
            }
            auto
              ca = fastcast!(TypeAlias) (resolveMyType(a)),
              cb = fastcast!(TypeAlias) (resolveMyType(b));
            if (!ca && !cb) return test(a == b);
            if ( ca && !cb) return false;
            if (!ca &&  cb) return false;
            if ( ca &&  cb) return (ca.name == cb.name) && ca.base == cb.base;
          }
          if (!gotImplicitCast(fp, (IType it) { return exactlyEqual(it, firstType); }))
            return fun;
          return new PrefixFunction(fp, fun);
        } else return obj;
      }
      Object tryIt() {
        if (auto res = sup.lookup(name, local))
          return funfilt(res);
        const string TRY = `
          if (auto res = sup.lookup(%%, local))
            return funfilt(res);
        `;
        foreach (prefix; prefixes)
          mixin(TRY.ctReplace("%%", "qformat(prefix, name)"));
        
        foreach (suffix; suffixes)
          mixin(TRY.ctReplace("%%", "qformat(name, suffix)"));
        
        foreach (suffix; suffixes)
          foreach (prefix; prefixes)
            mixin(TRY.ctReplace("%%", "qformat(prefix, name, suffix)"));
        
        return null;
      }
      if (auto res = tryIt()) return res;
      if (substituteDashes) {
        name = name.replace("-", "_");
        if (auto res = tryIt()) return res;
      }
      return null;
    }
  }
}

import ast.templ, ast.tuples;
class PrefixTemplate : ITemplate {
  Expr start; Template sup;
  string getIdentifier() { return sup.getIdentifier(); }
  this(Expr st, Template s) { start = st; sup = s; }
  override Object getInstanceIdentifier(IType it, ParseCb rest, string name) {
    
    IType[] suptypes;
    suptypes ~= start.valueType();
    if (auto tup = fastcast!(Tuple) (it)) suptypes ~= tup.types();
    else suptypes ~= it;
    
    IType suptype = mkTuple(suptypes);
    
    auto res = sup.getInstance(suptype, rest).lookup(name, true);
    if (auto fun = fastcast!(Function) (res)) {
      return new PrefixFunction(start, fun);
    }
    return res;
  }
}

Object gotModeDef(ref string text, ParseCb cont, ParseCb rest) {
  string ident;
  if (!text.gotIdentifier(ident))
    text.failparse("could not get mode def identifier");
  string par;
  text.gotIdentifier(par);
  Expr str;
  if (!rest(text, "tree.expr", &str))
    text.failparse("Couldn't get string param for mode def. ");
  auto sex = fastcast!(StringExpr)~ foldex(str);
  if (!sex)
    text.failparse("String literal expected! ");
  namespace().add(ident, new Mode(sex.str, par));
  if (!text.accept(";"))
    text.failparse("Expected a semicolon! ");
  return Single!(NoOp);
}
mixin DefaultParser!(gotModeDef, "tree.toplevel.defmode", null, "defmode");

Object gotMode(ref string text, ParseCb cont, ParseCb rest) {
  string name;
  if (!text.gotIdentifier(name))
    text.failparse("Mode name expected");
  auto mode = cast(Mode) namespace().lookup(name);
  if (!mode)
    text.failparse(name~" is not a mode! ");
  Expr arg;
  if (mode.argname) {
    if (!rest(text, "tree.expr _tree.expr.arith", &arg))
      text.failparse("Couldn't get mode argument! ");
  }
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  auto wrap = new Scope;
  namespace.set(wrap);
  
  auto ms = mode.translate(arg, rest);
  if (ms.firstParam) ms.firstParam = lvize(ms.firstParam);
  namespace.set(ms);
  
  Scope sc;
  if (!rest(text, "tree.scope", &sc))
    text.failparse("Couldn't parse mode scope! ");
  wrap.addStatement(sc);
  return wrap;
}
mixin DefaultParser!(gotMode, "tree.stmt.mode", "15", "mode");

Object gotPreSufFix(ref string text, bool isSuf, ParseCb cont, ParseCb rest) {
  string id;
  if (!text.gotIdentifier(id))
    text.failparse("Couldn't match prefix string");
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  auto wrap = new Scope;
  namespace.set(wrap);
  
  auto ms = new ModeSpace;
  if (isSuf) {
    ms.suffixes ~= id;
  } else {
    ms.prefixes ~= id;
  }
  namespace.set(ms);
  
  Scope sc;
  if (!rest(text, "tree.scope", &sc))
    text.failparse("Couldn't parse prefix scope! ");
  wrap.addStatement(sc);
  return wrap;
}
Object gotPrefix(ref string text, ParseCb cont, ParseCb rest) {
  return gotPreSufFix(text, false, cont, rest);
}
Object gotSuffix(ref string text, ParseCb cont, ParseCb rest) {
  return gotPreSufFix(text, true, cont, rest);
}
mixin DefaultParser!(gotPrefix, "tree.stmt.prefix", "155", "prefix");
mixin DefaultParser!(gotSuffix, "tree.stmt.suffix", "1551", "suffix");
