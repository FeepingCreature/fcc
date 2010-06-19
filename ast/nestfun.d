module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base, ast.variable, ast.pointer, ast.structure, ast.namespace;

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

void callNested(NestedFunction nf, Expr[] params, AsmFile dest) {
  assert(nf.type.ret.size == 4 || cast(Void) nf.type.ret);
  dest.comment("Begin nested call to ", nf);
  params ~= new Register!("ebp");
  foreach_reverse (param; params) {
    dest.comment("Push ", param);
    param.emitAsm(dest);
  }
  dest.put("call "~nf.mangleSelf);
  foreach (param; params) {
    dest.sfree(param.valueType().size);
  }
  if (!cast(Void) nf.type.ret) {
    dest.pushStack("%eax", nf.type.ret);
  }
}

class NestedCall : FunCall {
  override void emitAsm(AsmFile af) {
    callNested(cast(NestedFunction) fun, params, af);
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
