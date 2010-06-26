module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base,
       ast.variable, ast.pointer, ast.structure, ast.namespace,
       ast.vardecl, ast.parse, ast.assign, ast.constant;

class NestedFunction : Function {
  Scope context;
  this(Scope context) {
    this.context = context;
  }
  override {
    string mangleSelf() {
      return context.fun.mangleSelf() ~ "_subfun_" ~ context.fun.mangle(name, type);
    }
    string mangle(string name, Type type) {
      return mangleSelf() ~ "_" ~ name;
    }
    FunCall mkCall() {
      return new NestedCall;
    }
    int fixup() {
      auto cur = super.fixup();
      add(new Variable(Single!(Pointer, Single!(Void)), "__base_ptr", cur));
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
    
    if (auto nf = cast(NestedFunction) context.fun) {
      return nf.lookup(name, false, cast(Expr) lookup("__base_ptr", true, mybase), context);
    } else {
      auto sn = context.lookup(name),
            var = cast(Variable) sn;
      if (!var) return sn;
      return new MemberAccess_LValue(
        namespaceToStruct(context, cast(Expr) lookup("__base_ptr", true, mybase)),
        var.name
      );
    }
  }
}

void callNested(AsmFile dest, Type ret, Expr[] params, string callName, Expr dg = null) {
  assert(ret.size == 4 || cast(Void) ret);
  dest.comment("Begin nested call to ", callName);
  
  Expr dgs;
  if (dg) dgs = dgAsStruct(dg);
  
  if (dg) params ~= new MemberAccess_Expr(dgs, "data");
  else params ~= new Register!("ebp");
  
  foreach_reverse (param; params) {
    dest.comment("Push ", param);
    param.emitAsm(dest);
  }
  
  if (dg) {
    (new MemberAccess_Expr(dgs, "fun")).emitAsm(dest);
    dest.popStack("%eax", Single!(SizeT));
    dest.put("call *%eax");
  } else {
    dest.put("call "~callName);
  }
  foreach (param; params) {
    dest.sfree(param.valueType().size);
  }
  if (!cast(Void) ret) {
    dest.pushStack("%eax", ret);
  }
}

class NestedCall : FunCall {
  override void emitAsm(AsmFile af) {
    callNested(af, fun.type.ret, params, fun.mangleSelf);
  }
  override Type valueType() {
    return fun.type.ret;
  }
}

import parseBase, ast.modules, tools.log;
Object gotNestedFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto sc = cast(Scope) namespace();
  if (!sc) return null;
  auto nf = new NestedFunction(sc);
  // sup of nested funs isn't the surrounding function .. that's what context is for.
  auto mod = namespace().get!(Module)();
  if (auto res = cast(NestedFunction) gotGenericFunDef(nf, mod, text, cont, rest)) {
    logln("got nested fun def, setting sup to ", mod);
    mod.entries ~= cast(Tree) res;
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotNestedFunDef, "tree.stmt.nested_fundef");

class Delegate : Type {
  Type ret;
  Type[] args;
  this() { }
  this(NestedFunction nf) {
    ret = nf.type.ret;
    foreach (p; nf.type.params)
      args ~= p._0;
  }
  override int size() {
    return nativePtrSize * 2;
  }
  override string mangle() {
    auto res = "dg_ret_"~ret.mangle()~"_args";
    if (!args.length) res ~= "_none";
    else foreach (arg; args)
      res ~= "_"~arg.mangle();
    return res;
  }
}

Type dgAsStructType(Delegate dgtype) {
  return new Structure(null,
    [
      // TODO: Extend once function pointers are supported
      Structure.Member("fun", Single!(Pointer, Single!(Void))),
      Structure.Member("data", Single!(Pointer, Single!(Void)))
    ]
  );
}

import ast.casting;
Expr dgAsStruct(Expr ex) {
  auto dgtype = cast(Delegate) ex.valueType();
  assert(!!dgtype);
  if (auto lv = cast(LValue) ex) {
    return new ReinterpretCast!(LValue) (dgAsStructType(dgtype), lv);
  } else {
    return new ReinterpretCast!(Expr) (dgAsStructType(dgtype), ex);
  }
}

Object gotDgAsStruct(ref string st, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(st, "tree.expr ^selfrule", &ex))
    return null;
  if (!cast(Delegate) ex.valueType())
    return null;
  return cast(Object) dgAsStruct(ex);
}
mixin DefaultParser!(gotDgAsStruct, "tree.expr.dg_struct", "912");

class DgCall : Expr {
  Expr dg;
  Expr[] params;
  mixin defaultIterate!(dg, params);
  override void emitAsm(AsmFile af) {
    auto dgtype = cast(Delegate) dg.valueType();
    callNested(af, dgtype.ret, params, "delegate", dg);
  }
  override Type valueType() {
    return (cast(Delegate) dg.valueType()).ret;
  }
}

Object gotDgCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto dgtype = cast(Delegate) ex.valueType();
    if (!dgtype) return null;
    
    auto dc = new DgCall;
    dc.dg = ex;
    
    if (t2.accept("(")) {
      dc.params = matchCall(t2, Format("delegate ", ex), dgtype.args, rest);
      text = t2;
      return dc;
    } else return null;
  };
}
mixin DefaultParser!(gotDgCallExpr, "tree.rhs_partial.dgcall", null, true);

// &fun
class NestFunRefExpr : Expr {
  NestedFunction fun;
  mixin This!("fun");
  mixin defaultIterate!();
  override {
    Type valueType() {
      return new Delegate(fun);
    }
    void emitAsm(AsmFile af) {
      mkVar(af, dgAsStructType(cast(Delegate) valueType()), true, (Variable var) {
        (new Assignment((new MemberAccess_LValue(var, "fun")),
          new Constant(fun.mangleSelf()))).emitAsm(af);
        (new Assignment((new MemberAccess_LValue(var, "data")),
          new Register!("ebp"), true)).emitAsm(af);
      });
    }
  }
}

Object gotDgRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("&")) return null;
  
  string ident;
  if (!t2.gotIdentifier(ident, true)) return null;
  auto nf = cast(NestedFunction) namespace().lookup(ident);
  if (!nf) return null;
  
  text = t2;
  
  return new NestFunRefExpr(nf);
}
mixin DefaultParser!(gotDgRefExpr, "tree.expr.dg_ref", "210");

// stolen in turn from ast.fun
static this() {
  typeModlist ~= delegate Type(ref string text, Type cur, ParseCb, ParseCb rest) {
    Type ptype;
    Stuple!(Type, string)[] list;
    auto t2 = text;
    if (t2.accept("delegate") &&
      t2.gotParlist(list, rest)
    ) {
      text = t2;
      auto res = new Delegate;
      res.ret = cur;
      foreach (entry; list) res.args ~= entry._0;
      return res;
    } else return null;
  };
}
