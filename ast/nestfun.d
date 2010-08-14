module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base,
       ast.variable, ast.pointer, ast.structure, ast.namespace,
       ast.vardecl, ast.parse, ast.assign, ast.constant, ast.dg;

class NestedFunction : Function {
  Scope context;
  this(Scope context) {
    this.context = context;
  }
  override {
    string mangleSelf() {
      return context.fun.mangleSelf() ~ "_subfun_" ~ context.fun.mangle(name, type);
    }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    FunCall mkCall() {
      return new NestedCall;
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
      } else if (res) return res;
    }
    if (local
     || name == "__base_ptr"
     || name == "__old_ebp"
     || name == "__fun_ret") return null; // never recurse those
    assert(!!context);
    // logln("continuing lookup to ", name);
    
    if (auto nf = cast(NestedFunction) context.fun) {
      return nf.lookup(name, false, cast(Expr) lookup("__base_ptr", true, mybase), context);
    } else {
      auto sn = context.lookup(name, true),
            var = cast(Variable) sn;
      // logln("var: ", var, ", sn: ", sn, "; test ", context.lookup(name));
      // logln("context is ", context, " below fun ", context.fun);
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
  auto mod = namespace().get!(Module)();
  if (auto res = cast(NestedFunction) gotGenericFunDef(nf, mod, true, text, cont, rest)) {
    mod.entries ~= cast(Tree) res;
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotNestedFunDef, "tree.stmt.nested_fundef");

class NestedCall : FunCall {
  Expr dg;
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
  this(NestedFunction fun) {
    this.fun = fun;
    super(fun.getPointer(), new Register!("ebp"));
  }
  override string toString() {
    return Format("&", fun);
  }
  // TODO: emit asm directly in case of PointerFunction.
  override IType valueType() {
    return new Delegate(fun.type.ret, fun.type.params /map/ ex!("a, b -> a"));
  }
}

Object gotDgRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("&")) return null;
  
  string ident;
  Object obj;
  if (!rest(t2, "tree.expr", &obj)) return null;
  auto nf = cast(NestedFunction) obj;
  if (!nf) return null;
  
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

Object gotFunAsDgRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (!rest(t2, "tree.expr ^selfrule", &ex)) return null;
  auto fp = cast(FunctionPointer) ex.valueType();
  if (!fp) return null;
  text = t2;
  if (cast(Literal) ex)
    return new FunPtrAsDgExpr!(LitTemp)(ex);
  else
    return new FunPtrAsDgExpr!(mkDelegate)(ex);
}
mixin DefaultParser!(gotFunAsDgRefExpr, "tree.expr.fun_as_dg", "903");

// *fp
// TODO: this cannot work; it's too simple.
class PointerFunction(T) : T {
  Expr ptr;
  this(Expr ptr) {
    static if (is(typeof(super(null)))) super(null);
    this.ptr = ptr;
    New(type);
    auto dg = cast(Delegate) ptr.valueType();
    if (dg) {
      type.ret = dg.ret;
      type.params = dg.args /map/ (IType it) { return stuple(it, ""); };
    } else logln("TYPE ", ptr.valueType());
  }
  override {
    // edit: TOLD YA. Forgot this. Chased bugs for a good night.
    FunCall mkCall() { auto res = new NestedCall; res.dg = ptr; return res; }
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
