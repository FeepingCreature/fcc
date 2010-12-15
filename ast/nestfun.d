module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base,
       ast.variable, ast.pointer, ast.structure, ast.namespace,
       ast.vardecl, ast.parse, ast.assign, ast.constant, ast.dg;

class NestedFunction : Function {
  Scope context;
  this(Scope context) {
    this.context = context;
  }
  string cleaned_name() { return name.cleanup(); }
  override {
    string toString() { return "nested "~super.toString(); }
    string mangleSelf() {
      return context.get!(Function).mangleSelf() ~ "_subfun_" ~
        context.get!(Function).mangle(cleaned_name, type);
    }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ cleaned_name;
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
    Object lookup(string name, bool local = false) { return lookup(name, local, null, null); }
  }
  import tools.log;
  Object lookup(string name, bool local, Expr mybase, Scope context_override = null) {
    { // local lookup first
      Object res;
      if (context_override) res = context_override.lookup(name, true);
      else res = super.lookup(name, true);
      auto var = cast(Variable) res;
      if (mybase && var) {
        return new MemberAccess_LValue(
          namespaceToStruct(context_override?context_override:this, mybase),
          var.name
        );
      } else if (res) {
        if (auto nf = cast(NestedFunction) res) {
          return new PointerFunction!(NestedFunction) (new NestFunRefExpr(nf, mybase));
        }
        return res;
      }
    }
    if (local
     || name == "__base_ptr"
     || name == "__old_ebp"
     || name == "__fun_ret") return null; // never recurse those
    assert(!!context);
    // logln("continuing lookup to ", name);
    
    if (auto nf = cast(NestedFunction) context.get!(Function)) {
      return nf.lookup(name, false, cast(Expr) lookup("__base_ptr", true, mybase), context);
    } else {
      auto sn = context.lookup(name, true),
            var = cast(Variable) sn;
      // logln("var: ", var, ", sn: ", sn, "; test ", context.lookup(name));
      // logln("context is ", context, " below fun ", context.fun);
      if (auto nf = cast(NestedFunction) sn) {
        mybase = cast(Expr) lookup("__base_ptr", true, mybase);
        // see above
        return new PointerFunction!(NestedFunction) (new NestFunRefExpr(nf, mybase));
      }
      if (!var) return sn?sn:context.lookup(name, false);
      return new MemberAccess_LValue(
        namespaceToStruct(context, cast(Expr) lookup("__base_ptr", true, mybase)),
        var.name
      );
    }
  }
}

import parseBase, ast.modules, tools.log;
Object gotNestedFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto sc = cast(Scope) namespace();
  if (!sc) return null;
  auto nf = new NestedFunction(sc);
  // sup of nested funs isn't the surrounding function .. that's what context is for.
  auto mod = current_module();
  if (auto res = cast(NestedFunction) gotGenericFunDef(nf, mod, true, text, cont, rest)) {
    mod.entries ~= cast(Tree) res;
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotNestedFunDef, "tree.stmt.nested_fundef", "20");

Object gotNestedDgLiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = cast(Scope) namespace();
  if (!sc) return null;
  auto nf = new NestedFunction(sc);
  auto mod = current_module();
  auto res = cast(NestedFunction)
    gotGenericFunDef(nf, mod, true, t2, cont, rest, true /* noname */);
  if (!res)
    t2.failparse("Could not parse delegate literal");
  static int i;
  synchronized res.name = Format("__nested_dg_literal_", i++);
  text = t2;
  mod.entries ~= cast(Tree) res;
  return new NestFunRefExpr(res);
}
mixin DefaultParser!(gotNestedDgLiteral, "tree.expr.dgliteral", "2402", "delegate");

Object gotNestedFnLiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto fun = new Function();
  auto mod = current_module();
  auto res = cast(Function)
    gotGenericFunDef(fun, mod, true, t2, cont, rest, true /* noname */);
  
  if (!res)
    t2.failparse("Could not parse delegate literal");
  static int i;
  synchronized res.name = Format("__nested_fn_literal_", i++);
  text = t2;
  mod.entries ~= cast(Tree) res;
  return new FunRefExpr(res);
}
mixin DefaultParser!(gotNestedFnLiteral, "tree.expr.fnliteral", "2403", "function");

class NestedCall : FunCall {
  Expr dg;
  override NestedCall dup() {
    auto res = new NestedCall;
    res.fun = fun;
    foreach (entry; params) res.params ~= entry.dup;
    if (dg) res.dg = dg.dup;
    return res;
  }
  override void emitAsm(AsmFile af) {
    // if (dg) logln("call ", dg);
    // else logln("call {", fun.getPointer(), " @ebp");
    if (dg) callDg(af, fun.type.ret, params, dg);
    else callDg(af, fun.type.ret, params,
      new DgConstructExpr(fun.getPointer(), new Register!("ebp")));
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
    super(fun.getPointer(), base);
  }
  override string toString() {
    return Format("&", fun);
  }
  // TODO: emit asm directly in case of PointerFunction.
  override IType valueType() {
    return new Delegate(fun.type.ret, fun.type.params /map/ ex!("a, b -> a"));
  }
  override NestFunRefExpr dup() { return new NestFunRefExpr(fun, base); }
}

Object gotDgRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("&")) return null;
  
  string ident;
  NestedFunction nf;
  if (!rest(t2, "tree.expr _tree.expr.arith", &nf)) return null;
  
  text = t2;
  if (auto pnf = cast(PointerFunction!(NestedFunction)) nf) return cast(Object) pnf.ptr;
  if (auto  pf = cast(PointerFunction!(Function)) nf)       return cast(Object)  pf.ptr;
  return new NestFunRefExpr(nf);
}
mixin DefaultParser!(gotDgRefExpr, "tree.expr.dg_ref", "210");

import ast.int_literal;
// &fun as dg
class FunPtrAsDgExpr(T) : T {
  Expr ex;
  FunctionPointer fp;
  this(Expr ex) {
    this.ex = ex;
    fp = cast(FunctionPointer) ex.valueType();
    assert(!!fp);
    super(ex, new IntExpr(0));
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
      auto l2 = cast(Literal) ex;
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
    auto fp = cast(FunctionPointer) ex.valueType();
    if (!fp) return null;
    if (cast(Literal) ex)
      return new FunPtrAsDgExpr!(LitTemp)(ex);
    else
      return new FunPtrAsDgExpr!(mkDelegate)(ex);
  };
}

// *fp
// TODO: this cannot work; it's too simple.
class PointerFunction(T) : T {
  Expr ptr;
  this(Expr ptr) {
    static if (is(typeof(super(null)))) super(null);
    this.ptr = ptr;
    New(type);
    auto dg = cast(Delegate) ptr.valueType(), fp = cast(FunctionPointer) ptr.valueType();
    if (dg) {
      type.ret = dg.ret;
      type.params = dg.args /map/ (IType it) { return stuple(it, ""); };
    } else if (fp) {
      type.ret = fp.ret;
      type.params = fp.args /map/ (IType it) { return stuple(it, ""); };
    } else {
      logln("TYPE ", ptr.valueType());
      asm { int 3; }
    }
  }
  override {
    FunCall mkCall() {
      if (cast(Delegate) ptr.valueType()) {
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
  auto t2 = text;
  if (!t2.accept("*")) return null;
  
  Expr ex;
  if (!rest(t2, "tree.expr", &ex)) return null;
  auto fp = cast(FunctionPointer) ex.valueType(), dg = cast(Delegate) ex.valueType();
  if (!fp && !dg) return null;
  
  text = t2;
  
  if (dg) return new PointerFunction!(NestedFunction) (ex);
  else return new PointerFunction!(Function) (ex);
}
mixin DefaultParser!(gotFpDerefExpr, "tree.expr.fp_deref", "2102");
