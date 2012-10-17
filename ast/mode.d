module ast.mode;

import ast.base;
import
  ast.namespace, ast.fun, ast.fold, ast.literal_string, ast.scopes, ast.prefixfun,
  ast.withstmt, ast.casting, ast.pointer, ast.aliasing, ast.vardecl: lvize;

import tools.ctfe: ctReplace;
import tools.base: tolower, slice;

class Mode {
  string config;
  string argname;
  string ident;
  bool isGObjectMode() { return config.find("gobject-helper"[]) != -1; }
  bool isFreeMode() { return config.find("free-mode"[]) != -1 || isGObjectMode; }
  bool needsArg() {
    if (argname) return true;
    if (isGObjectMode) return true;
    return false;
  }
  this(string c, string a, string i) {
    config = c.replace("%IDENTIFIER"[], i);
    argname = a;
    ident = i;
  }
  ModeSpace translate(Expr ex, ParseCb rest) {
    auto res = new ModeSpace;
    string prefix, suffix;
    auto cfg = config.dup;
    while (cfg.length) {
      if (cfg.accept("free-mode"[])) continue;
      if (cfg.accept("prefix"[])) {
        if (!cfg.gotIdentifier(prefix))
          cfg.failparse("couldn't get prefix"[]);
        res.prefixes ~= prefix;
        continue;
      }
      
      if (cfg.accept("suffix"[])) {
        if (!cfg.gotIdentifier(suffix, false, true /* accept numbers */))
          cfg.failparse("couldn't get suffix"[]);
        res.suffixes ~= suffix;
        continue;
      }
      
      if (cfg.accept("gobject-helper"[])) {
        if (!ex) fail; // gobject always needs an ex
        res.fixupErrorsToNull = true;
        string capsname = ident;
        string leadcapsname, smallname = capsname.tolower();
        foreach (part; capsname.split("_"[])) {
          leadcapsname ~= part[0] ~ part[1..$].tolower();
        }
        if (cfg.accept("["[])) {
          leadcapsname = cfg.slice("]"[]);
        }
        res.prefixes ~= smallname ~ "_";
        // example: 
        // ClutterStage*:g_type_check_instance_cast(GTypeInstance*:obj, clutter_stage_get_type())
        string cast_expr =
          qformat(leadcapsname, "*: g_type_check_instance_cast(GTypeInstance*:obj, "[], smallname, "_get_type())"[]);
        auto lt = ex.valueType().llvmType();
        if (lt != "i32" && !lt.endsWith("*")) {
          logln("wth "[], lt, " ", ex.valueType());
          fail;
        }
        if (cfg.accept("boxed"[])) {
          res.firstParam = ex;
        } else {
          res.firstParam =
            iparse!(Expr, "gobject-hack"[], "tree.expr _tree.expr.arith"[])
                   (cast_expr,
                    namespace(), "obj"[], ex);
        }
        if (cfg.accept("<"[])) {
          string supertype;
          if (!cfg.gotIdentifier(supertype))
            cfg.failparse("couldn't get supertype"[]);
          if (!cfg.accept(">"[]))
            cfg.failparse("closing '>' expected"[]);
          auto sup_ms = fastcast!(Mode) (namespace().lookup(supertype));
          if (!sup_ms)
            cfg.failparse("Unknown mode "[], supertype);
          res.supmode = sup_ms.translate(ex, rest);
        }
        continue;
      }
      
      {
        auto backup = namespace();
        scope(exit) namespace.set(backup);
        // add the arg
        auto mns = fastalloc!(MiniNamespace)("mode_arg"[]);
        with (mns) {
          sup = backup;
          internalMode = true;
          if (argname) add(argname, ex);
        }
        namespace.set(mns);
        
        if (cfg.accept("first-arg"[])) {
          if (!rest(cfg, "tree.expr"[], &res.firstParam))
            cfg.failparse("Couldn't match first-arg arg! "[]);
          continue;
        }
      }
      cfg.failparse("Couldn't parse mode string"[]);
    }
    return res;
  }
}

import ast.int_literal;
class ModeSpace : RelNamespace, ScopeLike, IType /* hack for using with using */, ISafeSpaceTag {
  Namespace sup;
  Expr firstParam;
  string[] prefixes, suffixes;
  bool substituteDashes, fixupErrorsToNull;
  void fixupArgs(Argument[] args) {
    if (fixupErrorsToNull) {
      foreach (ref arg; args) {
        if (auto p1 = fastcast!(Pointer) (resolveType(arg.type))) {
          if (auto p2 = fastcast!(Pointer) (resolveType(p1.target))) {
            if (p2.target.mangle == "struct__GError") {
              arg.initEx = reinterpret_cast(arg.type, mkInt(0));
            }
          }
        }
      }
    }
  }
  ModeSpace supmode;
  this() { sup = namespace(); }
  override {
    Stuple!(IType, string)[] stackframe() { return (fastcast!(ScopeLike)(sup)).stackframe(); }
    string toString() { return Format("ModeSpace ("[], firstParam?firstParam.valueType():null, ")" /*" <- ", sup*/); }
    bool isTempNamespace() { return true; }
    bool returnsInMemory() {
      if (firstParam) return firstParam.valueType().returnsInMemory();
      return false;
    }
    string llvmType() {
      if (firstParam) return firstParam.valueType().llvmType();
      return "{}";
      // fail;
    }
    string llvmSize() {
      if (firstParam) return firstParam.valueType().llvmSize();
      // so you can have tuples including modes for stuff like using()
      // switch back if using ever handles (,) itself
      return "0";
      // assert(false);
    }
    string mangle() {
      if (firstParam) return "mode_override_for_"~firstParam.valueType().mangle;
      return qformat("modespace_", cast(int) this); // used for caching!
    }
    int opEquals(IType it) { return it is this; }
    // IType proxyType() { return null; }
    IType proxyType() { if (!firstParam) return null; return firstParam.valueType(); }
    bool isPointerLess() { if (!firstParam) return true; return firstParam.valueType().isPointerLess; }
    bool isComplete() { if (!firstParam) return true; return firstParam.valueType().isComplete; }
    mixin DefaultScopeLikeGuards!();
    Object lookupRel(string name, Expr context, bool isDirectLookup = true) {
      Object funfilt(Object obj, bool allowUnchangedOverload) {
        bool foundAnyFirstParSubsts;
        OverloadSet handleFun(ref Function fun) {
          // logln("handle ", fun, " !! ", firstParam, " !! ", fun.extern_c, " !! ", fun.type, " !! ", fun.type.params);
          if (!firstParam) {
            if (!fixupErrorsToNull) return null;
            fun = fun.flatdup;
            fun.type = fun.type.dup;
            fixupArgs(fun.type.params);
            return null;
          }
          if (!fun.extern_c) return null;
          if (!fun.type) return null;
          auto params = fun.type.params;
          if (!params.length) return null;
          auto firstType = params[0].type;
          // Expr fp = firstParam;
          Expr fp = reinterpret_cast(firstParam.valueType, context);
          if (!gotImplicitCast(fp, (IType it) { return exactlyEquals(it, firstType); })) {
            // logln("bail because mismatch: ", fp.valueType(), " against ", firstType);
            return null;
          }
          foundAnyFirstParSubsts = true;
          return fastalloc!(OverloadSet)(fun.name, fastalloc!(PrefixFunction)(fp, fun, &fixupArgs));
        }
        Extensible ext;
        if (auto fun = fastcast!(Function) (obj)) {
          ext = fastalloc!(OverloadSet)(fun.name);
          if (auto os = handleFun(fun))
            ext = ext.extend(os);
          if (!isDirectLookup)
            ext = ext.extend(fun);
        } else if (auto os = fastcast!(OverloadSet) (obj)) {
          ext = fastalloc!(OverloadSet)(os.name);
          foreach (fun; os.funs) {
            if (auto os2 = handleFun(fun))
              ext = ext.extend(os2);
            if (!isDirectLookup && allowUnchangedOverload)
              ext = ext.extend(fun);
          }
        }
        if (!ext || !fastcast!(OverloadSet) (ext).funs.length) ext = null;
        if (!ext) {
          if (isDirectLookup && context) if (auto tmpl = fastcast!(Template) (obj)) {
            return fastalloc!(PrefixTemplate)(context, tmpl);
          }
          if (isDirectLookup && !foundAnyFirstParSubsts) return null;
          return obj;
        }
        if (auto res = fastcast!(Object) (ext.simplify())) return res;
        return fastcast!(Object) (ext);
      }
      Object tryIt() {
        const string TRY = `
          if (auto res = sup.lookup(%%, false))
            reslist ~= funfilt(res, ??);
        `;
        // optimization: collapse em as they come
        Object[] reslist;
        foreach (prefix; prefixes)
          mixin(TRY.ctReplace("%%", "qformat(prefix, name)", "??", "true"));
        
        foreach (suffix; suffixes)
          mixin(TRY.ctReplace("%%", "qformat(name, suffix)", "??", "true"));
        
        if (prefixes && suffixes) {
          foreach (suffix; suffixes)
            foreach (prefix; prefixes)
              mixin(TRY.ctReplace("%%", "qformat(prefix, name, suffix)", "??", "true"));
        }
        
        if (supmode) {
          reslist ~= supmode.lookupRel(name, context, isDirectLookup);
        }
        
        if (firstParam) // otherwise, no point
          mixin(TRY.ctReplace("%%", "name", "??", "false"));
        
        if (!reslist.length) return null;
        if (auto ext = fastcast!(Extensible) (reslist[0])) {
          foreach (obj; reslist[1..$]) {
            if (auto e2 = fastcast!(Extensible) (obj))
              ext = extend_masked(ext, e2);
          }
          if (auto res = fastcast!(Object) (ext.simplify())) return res;
          return fastcast!(Object) (ext);
        }
        return reslist[0];
      }
      if (auto res = tryIt()) return res;
      if (substituteDashes) {
        name = name.replace("-"[], "_"[]);
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
      return fastalloc!(PrefixFunction)(start, fun);
    }
    return res;
  }
}

Object gotModeDef(ref string text, ParseCb cont, ParseCb rest) {
  string ident;
  if (!text.gotIdentifier(ident))
    text.failparse("could not get mode def identifier"[]);
  string par;
  text.gotIdentifier(par);
  Expr str;
  if (!rest(text, "tree.expr"[], &str))
    text.failparse("Couldn't get string param for mode def. "[]);
  auto sex = fastcast!(StringExpr)~ foldex(str);
  if (!sex)
    text.failparse("String literal expected! "[]);
  namespace().add(ident, fastalloc!(Mode)(sex.str, par, ident));
  if (!text.accept(";"[]))
    text.failparse("Expected a semicolon! "[]);
  return Single!(NoOp);
}
mixin DefaultParser!(gotModeDef, "tree.toplevel.defmode"[], null, "defmode"[]);

Object gotMode(ref string text, ParseCb cont, ParseCb rest) {
  bool gotMode;
  string t2 = text;
  if (t2.accept("mode"[])) gotMode = true;
  string name;
  if (!t2.gotIdentifier(name))
    if (!gotMode || namespace().lookup("mode"[])) return null;
    else t2.failparse("Mode name expected"[]);
  auto mode = cast(Mode) namespace().lookup(name);
  if (!mode)
    if (gotMode) text.failparse(name~" is not a mode! "[]);
    else return null;
  if (!gotMode && !mode.isFreeMode) return null;
  
  text = t2;
  
  Expr arg;
  if (mode.needsArg) {
    bool opened;
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    
    if (mode.isGObjectMode) {
      auto pre_ms = new ModeSpace;
      pre_ms.prefixes ~= mode.ident.tolower();
      pre_ms.prefixes ~= mode.ident;
      pre_ms.fixupErrorsToNull = true;
      namespace.set(fastalloc!(WithStmt)(fastalloc!(PlaceholderTokenLV)(pre_ms, "prefix/suffix pre thing"[])));
    } else {
      namespace.set(fastalloc!(WithStmt)(fastalloc!(PlaceholderTokenLV)(mode.translate(fastalloc!(PlaceholderToken)(Single!(Void), "bogus"[]), rest), "prefix/suffix pre thing 2"[])));
    }
    
    if (text.accept("("[])) opened = true;
    if (!rest(text, "tree.expr _tree.expr.arith"[], &arg))
      text.failparse("Couldn't get mode argument! "[]);
    if (opened && !text.accept(")"[]))
      text.failparse("Closing paren expected"[]);
  }
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  auto ms = mode.translate(arg, rest);
  if (ms.firstParam) return fastcast!(Object) (reinterpret_cast(ms, ms.firstParam));
  else return fastalloc!(PlaceholderTokenLV)(ms, "mode hack"[]);
}
mixin DefaultParser!(gotMode, "tree.expr.mode"[], "24053"[]);

Object gotPreSufFix(ref string text, bool isSuf, ParseCb cont, ParseCb rest) {
  string id;
  bool hadOpeningParen;
  if (text.accept("("[])) hadOpeningParen = true;
  if (isSuf) {
    if (!text.gotIdentifier(id, false, true /* allow number */))
      return null;
      // text.failparse("Couldn't match suffix string"[]);
  } else {
    if (!text.gotIdentifier(id))
      return null;
      // text.failparse("Couldn't match prefix string"[]);
  }
  if (hadOpeningParen && !text.accept(")"[]))
    text.failparse("Closing paren for pre/suffix argument expected"[]);
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  
  auto ms = new ModeSpace;
  if (isSuf) {
    ms.suffixes ~= id;
  } else {
    ms.prefixes ~= id;
  }
  
  return fastalloc!(PlaceholderTokenLV)(ms, "pre/suffix mode hack"[]);
}
Object gotPrefix(ref string text, ParseCb cont, ParseCb rest) {
  return gotPreSufFix(text, false, cont, rest);
}
Object gotSuffix(ref string text, ParseCb cont, ParseCb rest) {
  return gotPreSufFix(text, true, cont, rest);
}
mixin DefaultParser!(gotPrefix, "tree.expr.prefix"[], "240531"[], "prefix"[]);
mixin DefaultParser!(gotSuffix, "tree.expr.suffix"[], "240532"[], "suffix"[]);

static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto ms = fastcast!(ModeSpace) (ex.valueType());
    if (!ms || !ms.firstParam) return null;
    // logln("to == "[], ms.firstParam.valueType(), ", from == "[], ex);
    // logln("  ", resolveType(ms.firstParam.valueType()));
    return reinterpret_cast(ms.firstParam.valueType(), ex);
  };
  implicits ~= delegate Expr(Expr ex) {
    auto ms = fastcast!(ModeSpace) (ex.valueType());
    if (!ms || !ms.supmode) return null;
    return reinterpret_cast(ms.supmode, ex);
  };
}
