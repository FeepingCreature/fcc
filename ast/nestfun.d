module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base,
       ast.variable, ast.pointer, ast.structure, ast.namespace,
       ast.vardecl, ast.parse, ast.assign, ast.constant, ast.dg;

public import ast.fun: Argument;
import ast.aliasing, ast.casting, ast.opers;
class NestedFunction : Function {
  Namespace context;
  this(Namespace context) {
    this.context = context;
  }
  private this() { }
  string cleaned_name() { return name.cleanup(); }
  override {
    string toString() { return "nested "~super.toString(); }
    string mangleSelf() {
      return context.get!(Function).mangleSelf() ~ "_subfun_" ~
        context.get!(Function).mangle(cleaned_name, type)~"_of_"~type.mangle();
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
      add(new Variable(voidp, "__base_ptr", cur));
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
      fun = new PointerFunction!(NestedFunction)(new NestFunRefExpr(nf));
    }
    if (!res && !fun) return _res;
    // pointer to our immediate parent's base.
    // since this is a variable also, nesting rewrite will work correctly here
    auto ebp = fastcast!(Expr) (lookup("__base_ptr", true));
    if (!ebp) {
      logln("no base pointer found in ", this, "!!");
      asm { int 3; }
    }
    bool needsDup, checkDup;
    void convertToDeref(ref Iterable itr) {
      // do this first so that variable initializers get fixed up
      // but not our substituted __base_ptr.
      itr.iterate(&convertToDeref);
      if (auto var = fastcast!(Variable) (itr)) {
        if (checkDup) needsDup = true;
        else {
          auto type = var.valueType();
          // *type*:(void*:ebp + baseOffset)
          auto nuex = new DerefExpr(
            reinterpret_cast(new Pointer(type),
              lookupOp("+",
                reinterpret_cast(voidp, ebp),
                mkInt(var.baseOffset)
              )
            )
          );
          itr = fastcast!(Iterable) (nuex);
        }
      } else if (auto r = fastcast!(Register!("ebp")) (itr)) {
        if (checkDup) needsDup = true;
        else itr = fastcast!(Iterable) (reinterpret_cast(r.valueType(), ebp));
      }
    };
    auto itr = fastcast!(Iterable) (_res);
    if (fun) {
      checkDup = true;
      fun.iterateExpressions(&convertToDeref); checkDup = false;
      if (needsDup) {
        fun = fun.flatdup;
        fun.iterateExpressions(&convertToDeref);
        itr = fastcast!(Iterable) (fun);
      }
    } else {
      checkDup = true; convertToDeref(itr); checkDup = false;
      if (needsDup) {
        itr = itr.dup;
        convertToDeref(itr);
      }
    }
    return fastcast!(Object) (itr);
  }
}

import parseBase, ast.modules, tools.log;
Object gotNestedFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto ns = namespace(), sc = ns.get!(Scope); // might be in a template!!
  if (!sc) return null;
  // sup of nested funs isn't the surrounding function .. that's what context is for.
  auto mod = current_module();
  if (auto res = fastcast!(NestedFunction)~ gotGenericFunDef({
    return new NestedFunction(ns);
  }, mod, true, text, cont, rest)) {
    mod.entries ~= fastcast!(Tree)~ res;
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotNestedFunDef, "tree.stmt.nested_fundef", "20");

Object gotNestedDgLiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = namespace().get!(Scope);
  if (!sc) return null;
  auto nf = new NestedFunction(sc);
  auto mod = current_module();
  string name;
  static int i;
  synchronized name = Format("__nested_dg_literal_", i++);
  auto res = fastcast!(NestedFunction)~
    gotGenericFunDef(nf, mod, true, t2, cont, rest, name);
  if (!res)
    t2.failparse("Could not parse delegate literal");
  text = t2;
  mod.entries ~= fastcast!(Tree)~ res;
  return new NestFunRefExpr(res);
}
mixin DefaultParser!(gotNestedDgLiteral, "tree.expr.dgliteral", "2402", "delegate");

Object gotNestedFnLiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto fun = new Function();
  auto mod = current_module();
  string name;
  static int i;
  synchronized name = Format("__nested_fn_literal_", i++);
  auto res = fastcast!(Function)~
    gotGenericFunDef(fun, mod, true, t2, cont, rest, name);
  
  if (!res)
    t2.failparse("Could not parse delegate literal");
  text = t2;
  mod.entries ~= fastcast!(Tree)~ res;
  return new FunRefExpr(res);
}
mixin DefaultParser!(gotNestedFnLiteral, "tree.expr.fnliteral", "2403", "function");

class NestedCall : FunCall {
  Expr dg; Expr ebp; // may be substituted by a lookup
  override void iterate(void delegate(ref Iterable) dg2) {
    defaultIterate!(dg, ebp).iterate(dg2);
    super.iterate(dg2);
  }
  this() { ebp = new Register!("ebp"); }
  override NestedCall construct() { return new NestedCall; }
  override NestedCall dup() {
    NestedCall res = fastcast!(NestedCall) (super.dup());
    if (dg) res.dg = dg.dup;
    if (ebp) res.ebp = ebp.dup;
    return res;
  }
  override void emitAsm(AsmFile af) {
    // if (dg) logln("call ", dg);
    // else logln("call {", fun.getPointer(), " @ebp");
    if (dg) callDg(af, fun.type.ret, params, dg);
    else callDg(af, fun.type.ret, params,
      new DgConstructExpr(fun.getPointer(), ebp));
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
    if (!base) base = new Register!("ebp");
    this.fun = fun;
    this.base = base;
    // dup base so that iteration treats them separately. SUBTLE BUGFIX, DON'T CHANGE.
    super(fun.getPointer(), base.dup);
  }
  override void iterate(void delegate(ref Iterable) dg) {
    fun.iterateExpressions(dg);
    defaultIterate!(base).iterate(dg);
    super.iterate(dg);
  }
  override string toString() {
    return Format("&", fun, " (", super.data, ")");
  }
  // TODO: emit asm directly in case of PointerFunction.
  override IType valueType() {
    return new Delegate(fun.type.ret, fun.type.params);
  }
  override NestFunRefExpr dup() { return new NestFunRefExpr(fun, base.dup); }
}

Object gotDgRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  string ident;
  NestedFunction nf;
  if (!rest(text, "tree.expr _tree.expr.arith", &nf))
    return null;
  
  if (auto pnf = cast(PointerFunction!(NestedFunction)) nf) return fastcast!(Object)~ pnf.ptr;
  if (auto  pf = cast(PointerFunction!(Function)) nf)       return fastcast!(Object)~  pf.ptr;
  return new NestFunRefExpr(nf);
}
mixin DefaultParser!(gotDgRefExpr, "tree.expr.dg_ref", "210", "&");

import ast.int_literal;
// &fun as dg
class FunPtrAsDgExpr(T) : T {
  Expr ex;
  FunctionPointer fp;
  this(Expr ex) {
    this.ex = ex;
    fp = fastcast!(FunctionPointer)~ ex.valueType();
    assert(!!fp);
    super(ex, mkInt(0));
  }
  void iterate(void delegate(ref Itr) dg) {
    super.iterate(dg);
    defaultIterate!(ex).iterate(dg);
  }
  override string toString() {
    return Format("dg(", fp, ")");
  }
  // TODO: emit asm directly in case of PointerFunction.
  override IType valueType() {
    return new Delegate(fp.ret, fp.args);
  }
  override FunPtrAsDgExpr dup() { return new FunPtrAsDgExpr(ex); }
  static if (is(T: Literal)) {
    override string getValue() {
      auto l2 = fastcast!(Literal)~ ex;
      assert(!!l2, Format("Not a literal: ", ex));
      return l2.getValue()~", 0";
    }
  }
}

class LitTemp : mkDelegate, Literal {
  this(Expr a, Expr b) { super(a, b); }
  abstract override string getValue();
}

import ast.casting: implicits;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto fp = fastcast!(FunctionPointer)~ ex.valueType();
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
  void iterateExpressions(void delegate(ref Iterable) dg) {
    defaultIterate!(ptr).iterate(dg);
    super.iterateExpressions(dg);
  }
  this(Expr ptr) {
    static if (is(typeof(super(null)))) super(null);
    this.ptr = ptr;
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
      logln("TYPE ", ptr.valueType());
      asm { int 3; }
    }
  }
  override PointerFunction flatdup() { return new PointerFunction(ptr.dup); }
  override PointerFunction dup() { return new PointerFunction(ptr.dup); }
  override {
    FunCall mkCall() {
      if (fastcast!(Delegate)~ ptr.valueType()) {
        auto res = new NestedCall;
        res.fun = this;
        res.dg = ptr;
        return res;
      } else {
        auto res = new FunCall;
        res.fun = this;
        return res;
      }
      assert(false);
    }
    string mangleSelf() { asm { int 3; } }
    Expr getPointer() { return ptr; }
    string toString() {
      return Format("*", ptr);
    }
  }
}

Object gotFpDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr", &ex)) return null;
  auto fp = fastcast!(FunctionPointer)~ ex.valueType(), dg = fastcast!(Delegate)~ ex.valueType();
  if (!fp && !dg) return null;
  
  if (dg) return new PointerFunction!(NestedFunction) (ex);
  else return new PointerFunction!(Function) (ex);
}
mixin DefaultParser!(gotFpDerefExpr, "tree.expr.fp_deref", "2102", "*");
