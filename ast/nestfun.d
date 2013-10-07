module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base,
       ast.variable, ast.pointer, ast.structure, ast.namespace,
       ast.vardecl, ast.parse, ast.assign, ast.dg,
       ast.properties, ast.math, ast.fold, ast.tuples;

Function doBasePointerFixup(Function fun) {
  auto nf = fastcast!(NestedFunction) (fun), prev_nf = fastcast!(PointerFunction!(NestedFunction)) (fun);
  if (nf && !prev_nf) {
    // massive hack
    // this basically serves to introduce the EBP into the lookup, so that we can properly fix it up
    fun = new PointerFunction!(NestedFunction)(fastalloc!(NestFunRefExpr)(nf));
  }
  return fun;
}

public import ast.fun: Argument;
import ast.aliasing, ast.casting, ast.opers;
class NestedFunction : Function {
  Namespace context;
  this(Namespace context) {
    if (context) if (auto supfun = context.get!(Function)) {
      if (supfun.weak) markWeak();
    }
    this.context = context;
    this();
  }
  private this() { super(); }
  string cleaned_name() { return name.cleanup(); }
  override {
    bool isInternal() { return true; }
    Expr getPointer() { return fastalloc!(FunSymbol)(this, voidp); }
    Argument[] getParams(bool implicits) {
      auto res = super.getParams(false);
      if (implicits) {
        res ~= Argument(voidp, "__base_ptr");
        res ~= Argument(voidp, tlsbase);
      }
      return res;
    }
    string toString() { return "nested "~super.toString(); }
    string mangleSelf() {
      string supmang;
      if (auto ctx = context.get!(IsMangled)) supmang = ctx.mangleSelf();
      else if (auto ctx = context.get!(IType)) supmang = ctx.mangle();
      else assert(false, qformat("confusing context: ", context));
      return qformat(cleaned_name, "_of_", type.mangle(), "_under_", supmang);
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
      int id = super.fixup();
      inFixup = true; scope(exit) inFixup = false;
      // add(fastalloc!(Variable)(voidp, id++, "__base_ptr"));
      return id;
    }
  }
  import tools.log;
  override Object lookup(string name, bool local = false) {
    {
      auto res = super.lookup(name, true);
      if (res) return res;
      if (local) return null;
    }
    
    Expr ebp;
    void checkEBP() {
      // pointer to our immediate parent's base.
      // since this is a variable also, nesting rewrite will work correctly here
      ebp = fastcast!(Expr) (lookup("__base_ptr"[], true));
      if (!ebp) {
        logln("no base pointer found in "[], this, "!!"[]);
        fail;
      }
    }
    
    Object _res;
    auto rn = fastcast!(RelNamespace)(context);
    auto rt = fastcast!(hasRefType)(context);
    if (rn && rt) { // "static" lambda in class or struct
      // will get fixed up to __base_ptr, lol (total cheat)
      Expr base = reinterpret_cast(rt.getRefType(), new Register!("ebp"));
      _res = rn.lookupRel(name, base);
    }
    if (!_res) {
      // The reason we don't use sup here
      // is that nested functions are actually regular functions
      // declared at the top-level
      // that just HAPPEN to take an extra parameter
      // that points to the ebp of the lexically surrounding function
      // because of this, they must be compiled as if they're toplevel funs
      // but _lookup_ must proceed as if they're nested.
      // thus, sup vs. context.
      _res = context.lookup(name, false);
    }
    auto res = fastcast!(Expr) (_res);
    auto fun = fastcast!(Function) (_res);
    
    if (fun) fun = doBasePointerFixup(fun);
    else if (auto set = fastcast!(OverloadSet) (_res)) {
      Function[] funs2;
      foreach (fun2; set.funs) funs2 ~= doBasePointerFixup(fun2);
      foreach (ref fun2; funs2) {
        auto itr = fastcast!(Iterable) (fun2);
        if (!itr) fail;
        checkEBP;
        fixupEBP(itr, ebp);
        fun2 = fastcast!(Function) (itr);
      }
      return new OverloadSet(set.name, funs2);
    }
    if (!_res) {
      _res = lookupInImports(name, local);
    }
    if (!res && !fun && !fastcast!(Iterable)(_res)) return _res;
    if (res) _res = fastcast!(Object) (res);
    if (fun) _res = fastcast!(Object) (fun);
    auto itr = fastcast!(Iterable) (_res);
    checkEBP;
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
    mod.addEntry(res);
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
  
  Namespace context = sc;
  Expr contextptr = new Register!("ebp");
  
  if (!t2.accept("delegate"[])) {
    bool staticMode;
    if (t2.accept("static")) staticMode = true;
    if (t2.accept("\\") || t2.accept("λ")) {
      auto pos = lookupPos(text);
      synchronized name = Format("__nested_dg_literal_"[], i++, "_line_", pos._0);
      auto t3 = t2;
      
      if (staticMode) {
        context = context.get!(Function).sup;
        if (fastcast!(Module)(context)) {
          t2.failparse("what even happened there at ", sc);
        }
        contextptr = fastcast!(Expr)(sc.lookup("__base_ptr", true));
        if (!contextptr) {
          t2.failparse("failed to find context pointer");
        }
      }
      
      nf = fastalloc!(NestedFunction)(context);
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
      mod.addEntry(fastcast!(Tree) (res));
      return fastalloc!(NestFunRefExpr)(res, contextptr);
    }
    return null;
  }
  synchronized name = Format("__nested_dg_literal_"[], i++);
tryRegularDg:
  if (!nf) nf = fastalloc!(NestedFunction)(context);
  auto res = fastcast!(NestedFunction) (gotGenericFunDef(nf, mod, true, t2, cont, rest, name, shortform /* true when using the backslash-shortcut */));
  if (!res)
    t2.failparse("Could not parse delegate literal"[]);
  if (mod.doneEmitting) {
    t2.failparse("Internal compiler error: attempted to add nested dg literal to a module that was already emat: ", mod);
  }
  text = t2;
  mod.addEntry(fastcast!(Tree) (res));
  return fastalloc!(NestFunRefExpr)(res, contextptr);
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
  mod.addEntry(fastcast!(Tree) (res));
  return fastalloc!(FunRefExpr)(res);
}
mixin DefaultParser!(gotNestedFnLiteral, "tree.expr.fnliteral"[], "2403"[], "function"[]);

class NestedCall : FunCall {
  Expr dg; Expr ebp; // may be substituted by a lookup
  override void iterate(void delegate(ref Iterable) dg2, IterMode mode = IterMode.Lexical) {
    defaultIterate!(dg, ebp).iterate(dg2, mode);
    super.iterate(dg2, mode);
  }
  mixin defaultCollapse!();
  this() { ebp = new Register!("ebp"[]); }
  string toString() { return Format("dg "[], dg, "- "[], super.toString()); }
  Tree collapse() { return this; } // don't do the FunCall name replacers
  override NestedCall construct() { return new NestedCall; }
  override NestedCall dup() {
    NestedCall res = fastcast!(NestedCall) (super.dup());
    if (dg) res.dg = dg.dup;
    if (ebp) res.ebp = ebp.dup;
    return res;
  }
  override void emitWithArgs(LLVMFile lf, Expr[] args) {
    // if (dg) logln("call "[], dg);
    // else logln("call {"[], fun.getPointer(), " @ebp"[]);
    if (setup) setup.emitLLVM(lf);
    if (dg) callDg(lf, fun.type.ret, args, dg);
    else callDg(lf, fun.type.ret, args,
      optex(fastalloc!(DgConstructExpr)(fun.getPointer(), ebp)));
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

class LateLookupExpr : Expr {
  IType type;
  string name;
  this(string n, IType t) { name = n; type = t; }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    IType valueType() { return type; }
    LateLookupExpr dup() { return fastalloc!(LateLookupExpr)(name, type); }
    void emitLLVM(LLVMFile lf) {
      auto real_ex = fastcast!(Expr)(namespace().lookup(name));
      if (!real_ex) {
        logln("LateLookupExpr: no '", name, "' found at ", namespace());
        fail;
      }
      if (real_ex.valueType() != type) {
        logln("LateLookupExpr: real expr for '", name, "' had wrong type: ", real_ex.valueType());
        fail;
      }
      real_ex.emitLLVM(lf);
    }
  }
}

import ast.int_literal;
// &fun as dg
class FunPtrAsDgExpr(T) : T {
  Expr ex;
  FunctionPointer fp;
  this(Expr ex) {
    this.ex = ex;
    fp = fastcast!(FunctionPointer) (resolveType(ex.valueType()));
    if (!fp) { logln(ex); logln(fp); fail; }
    if (!fp.no_tls_ptr) asm { int 3; } // BADWRONG: THIS BREAKS UNDER MULTITHREADING
    auto tlsptr = fastalloc!(LateLookupExpr)(tlsbase, voidp);
    super(ex, tlsptr); // this call will have the tls pointer twice - but, meh!
  }
  void iterate(void delegate(ref Itr) dg, IterMode mode = IterMode.Lexical) {
    super.iterate(dg, mode);
    defaultIterate!(ex).iterate(dg, mode);
  }
  mixin defaultCollapse!();
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
  implicits ~= delegate Expr(Expr ex, IType dest) {
    if (fastcast!(HintType!(Tuple))(dest)) return null; // what
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
      // scope(failure) logln("test? dest ", dest);
      fun.parseMe;
      if (fun.type.ret)
        return ex;
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    auto fp = fastcast!(FunctionPointer) (resolveType(ex.valueType()));
    if (!fp || !fp.no_tls_ptr) return null; // can't convert tls ptr fun to dg
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
  mixin defaultCollapse!();
  this(Expr ptr, Statement setup = null) {
    static if (is(typeof(super(null)))) super(null);
    this.ptr = ptr;
    this.setup = setup;
    type = fastalloc!(FunctionType)();
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
  override PointerFunction flatdup() { auto res = fastalloc!(PointerFunction)(ptr.dup, setup); res.name = name; return res; }
  override PointerFunction dup() { auto res = fastalloc!(PointerFunction)(ptr.dup, setup); res.name = name; return res; }
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

pragma(set_attribute, C_mkPFNestFun, externally_visible);
extern(C) Function C_mkPFNestFun(Expr dgex) {
  return fastalloc!(PointerFunction!(NestedFunction))(dgex);
}

Object gotFpDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr _tree.expr.arith"[], &ex)) return null;
  auto fp = fastcast!(FunctionPointer)~ ex.valueType(), dg = fastcast!(Delegate)~ ex.valueType();
  if (!fp && !dg) return null;
  
  if (dg) return new PointerFunction!(NestedFunction) (ex);
  else return new PointerFunction!(Function) (ex);
}
mixin DefaultParser!(gotFpDerefExpr, "tree.expr.fp_deref"[], "2102"[], "*"[]);
