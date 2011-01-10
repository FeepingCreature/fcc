module ast.mode;

import ast.base;
import ast.namespace, ast.fun, ast.fold, ast.literal_string, ast.scopes, ast.casting, ast.pointer;

class Mode {
  string config;
  string argname;
  this(string c, string a) { config = c; argname = a; }
  ModeSpace translate(Expr ex, ParseCb rest) {
    auto res = new ModeSpace;
    res.sup = namespace();
    auto cfg = config;
    while (cfg.length) {
      if (cfg.accept("prefix")) {
        if (!cfg.gotIdentifier(res.prefix))
          cfg.failparse("couldn't get prefix");
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
  Function sup;
  this(Expr prefix, Function sup) {
    this.prefix = prefix;
    this.sup = sup;
    this.name = "[wrap]"~sup.name;
    assert(sup.extern_c);
    extern_c = true;
  }
  // this pains me.
  override {
    Expr getPointer() { logln("Can't get pointer to prefix-extended function! "); assert(false); }
    string toString() { return Format("prefix ", prefix, " to ", sup.toString()); }
    IType[] getParamTypes() { return sup.getParamTypes()[1 .. $]; }
    PrefixFunction alloc() { assert(false, "what"); }
    PrefixFunction dup() { return new PrefixFunction(prefix.dup(), sup.dup()); }
    PrefixCall mkCall() { return new PrefixCall(this, prefix, sup.mkCall()); }
    int fixup() { assert(false); } // this better be extern(C)
    string cleaned_name() { return sup.cleaned_name(); }
    string mangleSelf() { return sup.mangleSelf(); }
    string exit() { assert(false); }
    int framestart() { assert(false); }
    void emitAsm(AsmFile af) { assert(false); }
    Stuple!(IType, string, int)[] stackframe() { assert(false); }
    Object lookup(string name, bool local = false) { assert(false); }
  }
}

class PrefixCall : FunCall {
  FunCall sup;
  Expr prefix;
  this(Function fun, Expr prefix, FunCall sup) { this.fun = fun; this.prefix = prefix; this.sup = sup; }
  PrefixCall dup() { return new PrefixCall(fun, prefix.dup(), sup.dup()); }
  override void emitWithArgs(AsmFile af, Expr[] args) {
    sup.emitWithArgs(af, prefix ~ args);
  }
  override string toString() { return Format("prefixcall(", fun, " [prefix] ", prefix, " [regular] ", params, ")"); }
  override IType valueType() { return sup.valueType(); }
}

class ModeSpace : Namespace {
  Expr firstParam;
  string prefix;
  bool substituteDashes;
  override {
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() { return sup.stackframe(); }
    Object lookup(string name, bool local = false) {
      Object funfilt(Object obj) {
        if (auto fun = cast(Function) obj) {
          if (!firstParam) return fun;
          if (!fun.extern_c) return fun;
          if (!fun.type || !fun.type.params.length) return fun;
          auto firstType = fun.type.params[0]._0;
          Expr fp = firstParam;
          if (!gotImplicitCast(fp, (IType it) { return test(it == firstType); }))
            return fun;
          return new PrefixFunction(fp, fun);
        } else return obj;
      }
      Object tryIt() {
        if (auto res = sup.lookup(name, local))
          return funfilt(res);
        if (auto res = sup.lookup(qformat(prefix, name), local))
          return funfilt(res);
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

Object gotModeDef(ref string text, ParseCb cont, ParseCb rest) {
  string ident;
  if (!text.gotIdentifier(ident))
    text.failparse("could not get mode def identifier");
  string par;
  text.gotIdentifier(par);
  Expr str;
  if (!rest(text, "tree.expr", &str))
    text.failparse("Couldn't get string param for mode def. ");
  auto sex = cast(StringExpr) foldex(str);
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
  auto ms = mode.translate(arg, rest);
  namespace.set(ms);
  Scope sc;
  if (!rest(text, "tree.scope", &sc))
    text.failparse("Couldn't parse mode scope! ");
  return sc;
}
mixin DefaultParser!(gotMode, "tree.stmt.mode", "15", "mode");
