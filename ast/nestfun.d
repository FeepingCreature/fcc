module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base,
       ast.variable, ast.pointer, ast.structure, ast.namespace,
       ast.vardecl, ast.parse, ast.assign, ast.constant, ast.dg,
       ast.properties, ast.math;

public import ast.fun: Argument;
import ast.aliasing, ast.casting, ast.opers;
class NestedFunction : Function {
  Namespace context;
  this(Namespace context) {
    this.context = context;
    this();
  }
  private this() { super(); }
  string cleaned_name() { return name.cleanup(); }
  override {
    string toString() { return "nested "~super.toString(); }
    string mangleSelf() {
      return cleaned_name~"_of_"~type.mangle()~"_under_"~context.get!(Function).mangleSelf();
    }
    NestedFunction alloc() { return new NestedFunction; }
    NestedFunction flatdup() {
      auto res = fastcast!(NestedFunction) (super.flatdup());
      res.context = context;
      return res;
    }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    FunCall mkCall() {
      auto res = new NestedCall;
      res.fun = this;
      return res;
    }
    int fixup() {
      auto cur = super.fixup();
      inFixup = true; scope(exit) inFixup = false;
      add(fastalloc!(Variable)(voidp, "__base_ptr"[], cur));
      _framestart += 4;
      cur += 4;
      return cur;
    }
  }
  import tools.log;
  override Object lookup(string name, bool local = false) {
    {
      auto res = super.lookup(name, true);
      if (res) return res;
      if (local) return null;
    }
    // The reason we don't use sup here
    // is that nested functions are actually regular functions
    // declared at the top-level
    // that just HAPPEN to take an extra parameter
    // that points to the ebp of the lexically surrounding function
    // because of this, they must be compiled as if they're toplevel funs
    // but _lookup_ must proceed as if they're nested.
    // thus, sup vs. context.
    auto _res = context.lookup(name, false);
    auto res = fastcast!(Expr) (_res);
    auto fun = fastcast!(Function) (_res);
    auto nf = fastcast!(NestedFunction) (fun), prev_nf = fastcast!(PointerFunction!(NestedFunction)) (fun);
    if (nf && !prev_nf) {
      // massive hack
      // this basically serves to introduce the EBP into the lookup, so that we can properly fix it up
      fun = new PointerFunction!(NestedFunction)(fastalloc!(NestFunRefExpr)(nf));
    }
    if (!_res) {
      _res = lookupInImports(name, local);
    }
    if (!res && !fun) return _res;
    if (res) _res = fastcast!(Object) (res);
    if (fun) _res = fastcast!(Object) (fun);
    // pointer to our immediate parent's base.
    // since this is a variable also, nesting rewrite will work correctly here
    auto ebp = fastcast!(Expr) (lookup("__base_ptr"[], true));
    if (!ebp) {
      logln("no base pointer found in "[], this, "!!"[]);
      fail;
    }
    auto itr = fastcast!(Iterable) (_res);
    fixupEBP(itr, ebp);
    return fastcast!(Object) (itr);
  }
}

import parseBase, ast.modules, tools.log;
Object gotNestedFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto ns = namespace(), sc = ns.get!(Scope); // might be in a template!!
  if (!sc) return null;
  // sup of nested funs isn't the surrounding function .. that's what context is for.
  auto mod = fastcast!(Module) (current_module());
  if (auto res = fastcast!(NestedFunction)~ gotGenericFunDef({
    return fastalloc!(NestedFunction)(ns);
  }, mod, true, text, cont, rest)) {
    // do this HERE, so we get the right context
    // and don't accidentally see variables defined further down!
    res.parseMe;
    mod.entries ~= fastcast!(Tree)~ res;
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotNestedFunDef, "tree.stmt.nested_fundef"[], "20"[]);

import ast.returns;
Object gotNestedDgLiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = namespace().get!(Scope);
  if (!sc) return null;
  NestedFunction nf;
  auto mod = fastcast!(Module) (current_module());
  string name;
  static int i;
  bool shortform;
  if (!t2.accept("delegate"[])) {
    if (t2.accept("\\") || t2.accept("λ")) {
      synchronized name = Format("__nested_dg_literal_"[], i++);
      auto t3 = t2;
      nf = fastalloc!(NestedFunction)(sc);
      auto res = fastcast!(NestedFunction) (gotGenericFunDeclNaked(nf, mod, true, t3, cont, rest, name, true));
      if (!t3.accept("->"[])) {
        t3.setError("missing result-arrow for lambda"[]);
        shortform = true;
        nf = null;
        goto tryRegularDg;
      }
      t2 = t3;
      auto backup = namespace();
      scope(exit) namespace.set(backup);
      
      namespace.set(res);
      auto sc2 = new Scope;
      namespace.set(sc2);
      
      *octoless_marker.ptr() = t2;
      scope(exit) *octoless_marker.ptr() = null;
      
      Expr ex;
      if (!rest(t2, "tree.expr"[], &ex))
        t2.failparse("Expected result expression for lambda"[]);
      res.type.ret = ex.valueType();
      
      sc2.addStatement(fastalloc!(ReturnStmt)(ex));
      res.addStatement(sc2);
      
      text = t2;
      mod.entries ~= fastcast!(Tree) (res);
      return fastalloc!(NestFunRefExpr)(res);
    }
    return null;
  }
  synchronized name = Format("__nested_dg_literal_"[], i++);
tryRegularDg:
  if (!nf) nf = fastalloc!(NestedFunction)(sc);
  auto res = fastcast!(NestedFunction) (gotGenericFunDef(nf, mod, true, t2, cont, rest, name, shortform /* true when using the backslash-shortcut */));
  if (!res)
    t2.failparse("Could not parse delegate literal"[]);
  if (mod.alreadyEmat) {
    t2.failparse("Internal compiler error: attempted to add nested dg literal to a module that was already emat: ", mod);
  }
  text = t2;
  mod.entries ~= fastcast!(Tree)~ res;
  return fastalloc!(NestFunRefExpr)(res);
}
mixin DefaultParser!(gotNestedDgLiteral, "tree.expr.dgliteral"[], "2402"[]);

Object gotNestedFnLiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto fun = fastalloc!(Function)();
  auto mod = fastcast!(Module) (current_module());
  string name;
  static int i;
  synchronized name = Format("__nested_fn_literal_"[], i++);
  auto res = fastcast!(Function)~
    gotGenericFunDef(fun, mod, true, t2, cont, rest, name);
  
  if (!res)
    t2.failparse("Could not parse delegate literal"[]);
  text = t2;
  mod.entries ~= fastcast!(Tree)~ res;
  return fastalloc!(FunRefExpr)(res);
}
mixin DefaultParser!(gotNestedFnLiteral, "tree.expr.fnliteral"[], "2403"[], "function"[]);

class NestedCall : FunCall {
  Expr dg; Expr ebp; // may be substituted by a lookup
  override void iterate(void delegate(ref Iterable) dg2, IterMode mode = IterMode.Lexical) {
    defaultIterate!(dg, ebp).iterate(dg2, mode);
    super.iterate(dg2, mode);
  }
  this() { ebp = new Register!("ebp"[]); }
  string toString() { return Format("dg "[], dg, "- "[], super.toString()); }
  override NestedCall construct() { return new NestedCall; }
  override NestedCall dup() {
    NestedCall res = fastcast!(NestedCall) (super.dup());
    if (dg) res.dg = dg.dup;
    if (ebp) res.ebp = ebp.dup;
    return res;
  }
  override void emitWithArgs(AsmFile af, Expr[] args) {
    // if (dg) logln("call "[], dg);
    // else logln("call {"[], fun.getPointer(), " @ebp"[]);
    if (setup) setup.emitAsm(af);
    if (dg) callDg(af, fun.type.ret, args, dg);
    else callDg(af, fun.type.ret, args,
      fastalloc!(DgConstructExpr)(fun.getPointer(), ebp));
  }
  override IType valueType() {
    return fun.type.ret;
  }
}

// &fun
class NestFunRefExpr : mkDelegate {
  NestedFunction fun;
  Expr base;
  this(NestedFunction fun, Expr base = null) {
    if (!base) base = new Register!("ebp"[]);
    this.fun = fun;
    this.base = base;
    // dup base so that iteration treats them separately. SUBTLE BUGFIX, DON'T CHANGE.
    super(fun.getPointer(), base.dup);
  }
  override void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    fun.iterate(dg, IterMode.Semantic);
    defaultIterate!(base).iterate(dg, mode);
    super.iterate(dg, mode);
  }
  override string toString() {
    return Format("&"[], fun, " ("[], super.data, ")"[]);
  }
  // TODO: emit asm directly in case of PointerFunction.
  override IType valueType() {
    return fastalloc!(Delegate)(fun.type);
  }
  override NestFunRefExpr dup() { return fastalloc!(NestFunRefExpr)(fun, base.dup); }
}

Object gotDgRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  string ident;
  NestedFunction nf;
  
  auto propbackup = propcfg().withCall;
  propcfg().withCall = false;
  scope(exit) propcfg().withCall = propbackup;
  
  if (!rest(text, "tree.expr _tree.expr.arith"[], &nf))
    return null;
  
  if (auto pnf = cast(PointerFunction!(NestedFunction)) nf) return fastcast!(Object)~ pnf.ptr;
  if (auto  pf = cast(PointerFunction!(Function)) nf)       return fastcast!(Object)~  pf.ptr;
  return fastalloc!(NestFunRefExpr)(nf);
}
mixin DefaultParser!(gotDgRefExpr, "tree.expr.dg_ref"[], "210"[], "&"[]);

import ast.int_literal;
// &fun as dg
class FunPtrAsDgExpr(T) : T {
  Expr ex;
  FunctionPointer fp;
  this(Expr ex) {
    this.ex = ex;
    fp = fastcast!(FunctionPointer) (resolveType(ex.valueType()));
    if (!fp) { logln(ex); logln(fp); fail; }
    super(ex, mkInt(0));
  }
  void iterate(void delegate(ref Itr) dg, IterMode mode = IterMode.Lexical) {
    super.iterate(dg, mode);
    defaultIterate!(ex).iterate(dg, mode);
  }
  override string toString() {
    return Format("dg("[], fp, ")"[]);
  }
  // TODO: emit asm directly in case of PointerFunction.
  override IType valueType() {
    return fastalloc!(Delegate)(fp.ret, fp.args);
  }
  override FunPtrAsDgExpr dup() { return fastalloc!(FunPtrAsDgExpr)(ex); }
  static if (is(T: Literal)) {
    override string getValue() {
      auto l2 = fastcast!(Literal)~ ex;
      assert(!!l2, Format("Not a literal: "[], ex));
      return l2.getValue()~"[], 0";
    }
  }
}

class LitTemp : mkDelegate, Literal {
  this(Expr a, Expr b) { super(a, b); }
  abstract override string getValue();
}

import ast.casting: implicits;
static this() {
  // the next two implicits are BLATANT cheating.
  implicits ~= delegate Expr(Expr ex, IType hint) {
    if (!hint) return null;
    auto dg = fastcast!(Delegate) (resolveType(hint));
    if (!dg) return null;
    if (auto nfr = fastcast!(NestFunRefExpr) (ex)) {
      auto fun = nfr.fun;
      auto type1 = fun.type, type2 = dg.ft;
      if (type1.args_open) {
        auto params1 = type1.params;
        auto params2 = type2.params;
        if (params1.length != params2.length) return null;
        // logln("fixup! [1 ", params1, "] [2", params2, "]");
        foreach (i, ref p1; params1) {
          auto p2 = params2[i];
          if (p1.type && p2.type && p1.type != p2.type) {
            logln("oh shit");
            logln(":", type1);
            logln(":", type2);
            asm { int 3; }
          }
          if (!p1.type) p1.type = p2.type;
        }
        if (!type1.args_open) {
          fun.fixup;
        }
        // logln(" => ", fun.tree);
      }
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    auto nfr = fastcast!(NestFunRefExpr) (ex);
    if (!nfr) {
      auto dg = fastcast!(Delegate) (resolveType(ex.valueType()));
      if (dg && !dg.ret) {
        logln("huh. ", ex);
        logln(".. ", fastcast!(Object) (ex).classinfo.name);
        fail;
      }
      return null;
    }
    auto fun = nfr.fun;
    if (!fun.type.ret) {
      fun.parseMe;
      if (fun.type.ret)
        return ex;
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    auto fp = fastcast!(FunctionPointer) (resolveType(ex.valueType()));
    if (!fp) return null;
    if (fastcast!(Literal)~ ex)
      return new FunPtrAsDgExpr!(LitTemp)(ex);
    else
      return new FunPtrAsDgExpr!(mkDelegate)(ex);
  };
}

// *fp
// TODO: this cannot work; it's too simple.
class PointerFunction(T) : T {
  Expr ptr;
  Statement setup;
  override void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    defaultIterate!(ptr, setup).iterate(dg, mode);
    super.iterate(dg, IterMode.Semantic);
  }
  this(Expr ptr, Statement setup = null) {
    static if (is(typeof(super(null)))) super(null);
    this.ptr = ptr;
    this.setup = setup;
    New(type);
    auto dg = fastcast!(Delegate)~ ptr.valueType(), fp = fastcast!(FunctionPointer)~ ptr.valueType();
    if (dg) {
      type.ret = dg.ret;
      type.params = dg.args.dup;
    } else if (fp) {
      type.ret = fp.ret;
      type.params = fp.args.dup;
      type.stdcall = fp.stdcall;
    } else {
      logln("TYPE "[], ptr.valueType());
      fail;
    }
  }
  override PointerFunction flatdup() { return fastalloc!(PointerFunction)(ptr.dup, setup); }
  override PointerFunction dup() { return fastalloc!(PointerFunction)(ptr.dup, setup); }
  override {
    FunCall mkCall() {
      if (fastcast!(Delegate)~ ptr.valueType()) {
        auto res = new NestedCall;
        res.fun = this;
        res.dg = ptr;
        res.setup = setup;
        return res;
      } else {
        auto res = new FunCall;
        res.setup = setup;
        res.fun = this;
        return res;
      }
      assert(false);
    }
    string mangleSelf() { fail; return ""; }
    Expr getPointer() { if (setup) return fastalloc!(StatementAndExpr)(setup, ptr); return ptr; }
    string toString() {
      return Format("*"[], ptr);
    }
  }
}

Object gotFpDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr"[], &ex)) return null;
  auto fp = fastcast!(FunctionPointer)~ ex.valueType(), dg = fastcast!(Delegate)~ ex.valueType();
  if (!fp && !dg) return null;
  
  if (dg) return new PointerFunction!(NestedFunction) (ex);
  else return new PointerFunction!(Function) (ex);
}
mixin DefaultParser!(gotFpDerefExpr, "tree.expr.fp_deref"[], "2102"[], "*"[]);
