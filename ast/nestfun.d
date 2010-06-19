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
      logln("add base pointer in fixup");
      add(new Variable(Single!(Pointer, Single!(Void)), "__base_ptr", cur));
      cur += 4;
      return cur;
    }
    Object lookup(string name) { return lookup(name, null); }
  }
  Object lookup(string name, Expr baseptr) {
    foreach (entry; field)
      if (entry._0 == name) {
        auto var = cast(Variable) entry._1;
        if (baseptr && var) {
          return new MemberAccess_LValue(
            scopeToStruct(context, baseptr),
            var.name
          );
        } else return entry._1;
      }
    if (name == "__base_ptr"
    || name == "__old_ebp"
    || name == "__fun_ret") return null; // never recurse those
    assert(context);
    if (!baseptr) baseptr = cast(Expr) lookup("__base_ptr", null);
    assert(!!baseptr, Format("Cannot lookup base pointer @", this.name, " looking up ", name));
    
    if (auto nf = cast(NestedFunction) context.fun) {
      return nf.lookup(name, cast(Expr) nf.lookup("__base_ptr", baseptr));
    } else {
      auto sn = context.lookup(name),
            var = cast(Variable) sn;
      if (!var) return sn;
      logln("resolve via baseptr ", baseptr, ": ", var);
      logln("scope as struct: ", scopeToStruct(context, baseptr)); 
      return new MemberAccess_LValue(
        scopeToStruct(context, baseptr),
        var.name
      );
    }
  }
}

import tools.log;
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

import parseBase, ast.modules;
Object gotNestedFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto sc = cast(Scope) namespace();
  if (!sc) return null;
  auto nf = new NestedFunction(sc);
  if (auto res = gotGenericFunDef(nf, text, cont, rest)) {
    namespace().get!(Module)().entries ~= cast(Tree) res;
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotNestedFunDef, "tree.stmt.nested_fundef");
