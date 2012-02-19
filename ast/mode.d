module ast.mode;

import ast.base;
import
  ast.namespace, ast.fun, ast.fold, ast.literal_string, ast.scopes,
  ast.withstmt, ast.casting, ast.pointer, ast.aliasing, ast.vardecl: lvize;

import tools.ctfe: ctReplace;
import tools.base: tolower;

class Mode {
  string config;
  string argname;
  string ident;
  bool isGObjectMode() { return config.find("gobject-helper") != -1; }
  bool isFreeMode() { return isGObjectMode; }
  bool needsArg() {
    if (argname) return true;
    if (isGObjectMode) return true;
    return false;
  }
  this(string c, string a, string i) { config = c; argname = a; ident = i; }
  ModeSpace translate(Expr ex, ParseCb rest) {
    auto res = new ModeSpace;
    string prefix, suffix;
    auto cfg = config.dup;
    while (cfg.length) {
      if (cfg.accept("prefix")) {
        if (!cfg.gotIdentifier(prefix))
          cfg.failparse("couldn't get prefix");
        res.prefixes ~= prefix;
        continue;
      }
      
      if (cfg.accept("suffix")) {
        if (!cfg.gotIdentifier(suffix, false, true /* accept numbers */))
          cfg.failparse("couldn't get suffix");
        res.suffixes ~= suffix;
        continue;
      }
      
      if (cfg.accept("gobject-helper")) {
        string capsname = ident;
        string leadcapsname, smallname = capsname.tolower();
        foreach (part; capsname.split("_")) {
          leadcapsname ~= part[0] ~ part[1..$].tolower();
        }
        res.prefixes ~= smallname ~ "_";
        // example: 
        // ClutterStage*:g_type_check_instance_cast(GTypeInstance*:obj, clutter_stage_get_type())
        string cast_expr =
          qformat(leadcapsname, "*: g_type_check_instance_cast(GTypeInstance*:obj, ", smallname, "_get_type())");
        if (ex.valueType().size != 4) {
          logln("wth ", ex.valueType());
          fail;
        }
        res.firstParam =
          iparse!(Expr, "gobject-hack", "tree.expr _tree.expr.arith")
                 (cast_expr,
                  namespace(), "obj", ex);
        if (cfg.accept("<")) {
          string supertype;
          if (!cfg.gotIdentifier(supertype))
            cfg.failparse("couldn't get supertype");
          if (!cfg.accept(">"))
            cfg.failparse("closing '>' expected");
          auto sup_ms = fastcast!(Mode) (namespace().lookup(supertype));
          if (!sup_ms)
            cfg.failparse("Unknown mode ", supertype);
          res.supmode = sup_ms.translate(ex, rest);
        }
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
  Expr[] getParams() { return sup.getParams() ~ prefix ~ super.getParams(); }
  private this() { }
  PrefixCall dup() {
    auto res = new PrefixCall(fun.flatdup, prefix.dup, sup.dup);
    foreach (param; params) res.params ~= param.dup;
    return res;
  }
  override void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    defaultIterate!(prefix).iterate(dg, mode);
    sup.iterate(dg, mode);
    super.iterate(dg, mode);
  }
  override void emitWithArgs(AsmFile af, Expr[] args) {
    sup.emitWithArgs(af, prefix ~ args);
  }
  override string toString() { return Format("prefixcall(", fun, " [prefix] ", prefix, " [rest] ", sup, ": ", super.getParams(), ")"); }
  override IType valueType() { return sup.valueType(); }
}

class ModeSpace : RelNamespace, ScopeLike, IType /* hack for using with using */ {
  Namespace sup;
  Expr firstParam;
  string[] prefixes, suffixes;
  bool substituteDashes;
  ModeSpace supmode;
  this() { sup = namespace(); }
  override {
    int framesize() { return (fastcast!(ScopeLike)~ sup).framesize(); }
    string toString() { return Format("ModeSpace (", firstParam?firstParam.valueType():null, ") <- ", sup); }
    bool isTempNamespace() { return true; }
    int size() {
      if (firstParam) return firstParam.valueType().size;
      assert(false);
    }
    string mangle() { assert(false); }
    ubyte[] initval() { assert(false); }
    int opEquals(IType it) { return it is this; }
    IType proxyType() { return null; }
    bool isPointerLess() { if (!firstParam) return true; return firstParam.valueType().isPointerLess; }
    bool isComplete() { if (!firstParam) return true; return firstParam.valueType().isComplete; }
    mixin DefaultScopeLikeGuards!();
    Object lookupRel(string name, Expr context) {
      Object funfilt(Object obj) {
        OverloadSet handleFun(Function fun) {
          if (!firstParam) return null;
          if (!fun.extern_c) return null;
          if (!fun.type) return null;
          auto params = fun.type.params;
          if (!params.length) return null;
          auto firstType = params[0].type;
          // Expr fp = firstParam;
          Expr fp = reinterpret_cast(firstParam.valueType, context);
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
            return null;
          return new OverloadSet(fun.name, new PrefixFunction(fp, fun));
        }
        Extensible ext;
        if (auto fun = fastcast!(Function) (obj)) {
          ext = new OverloadSet(fun.name);
          if (auto os = handleFun(fun))
            ext = ext.extend(os);
          else
            ext = ext.extend(fun);
        } else if (auto os = fastcast!(OverloadSet) (obj)) {
          ext = new OverloadSet(os.name);
          foreach (fun; os.funs)
            if (auto os2 = handleFun(fun))
              ext = ext.extend(os2);
            else
              ext = ext.extend(fun);
        }
        if (!ext) return obj;
        if (auto res = fastcast!(Object) (ext.simplify())) return res;
        return fastcast!(Object) (ext);
      }
      Object tryIt() {
        const string TRY = `
          if (auto res = sup.lookup(%%, false))
            return funfilt(res);
        `;
        mixin(TRY.ctReplace("%%", "name"));
        
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
      if (supmode)
        if (auto res = supmode.lookupRel(name, context))
          return res;
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
  namespace().add(ident, new Mode(sex.str, par, ident));
  if (!text.accept(";"))
    text.failparse("Expected a semicolon! ");
  return Single!(NoOp);
}
mixin DefaultParser!(gotModeDef, "tree.toplevel.defmode", null, "defmode");

Object gotMode(ref string text, ParseCb cont, ParseCb rest) {
  bool gotMode;
  string t2 = text;
  if (t2.accept("mode")) gotMode = true;
  string name;
  if (!t2.gotIdentifier(name))
    if (gotMode) t2.failparse("Mode name expected");
    else return null;
  auto mode = cast(Mode) namespace().lookup(name);
  if (!mode)
    if (gotMode) text.failparse(name~" is not a mode! ");
    else return null;
  if (!gotMode && !mode.isFreeMode) return null;
  
  text = t2;
  
  Expr arg;
  if (mode.needsArg) {
    bool opened;
    if (text.accept("(")) opened = true;
    if (!rest(text, "tree.expr _tree.expr.arith", &arg))
      text.failparse("Couldn't get mode argument! ");
    if (opened && !text.accept(")"))
      text.failparse("Closing paren expected");
  }
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  auto ms = mode.translate(arg, rest);
  if (ms.firstParam) return fastcast!(Object) (reinterpret_cast(ms, ms.firstParam));
  else return new PlaceholderTokenLV(ms, "mode hack");
}
mixin DefaultParser!(gotMode, "tree.expr.mode", "24053");

Object gotPreSufFix(ref string text, bool isSuf, ParseCb cont, ParseCb rest) {
  string id;
  if (isSuf) {
    if (!text.gotIdentifier(id, false, true /* allow number */))
      text.failparse("Couldn't match suffix string");
  } else {
    if (!text.gotIdentifier(id))
      text.failparse("Couldn't match prefix string");
  }
  
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
  auto that_ex = new PlaceholderTokenLV(ms, "prefix/suffix thing");
  namespace.set(new WithStmt(that_ex));
  
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
mixin DefaultParser!(gotPrefix, "tree.stmt.prefix", "601", "prefix");
mixin DefaultParser!(gotSuffix, "tree.stmt.suffix", "602", "suffix");

static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto vt = ex.valueType();
    auto ms = fastcast!(ModeSpace) (vt);
    if (!ms || !ms.firstParam) return null;
    // logln("to == ", ms.firstParam.valueType(), ", from == ", ex);
    return reinterpret_cast(ms.firstParam.valueType(), ex);
  };
}
