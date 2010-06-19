module ast.nestfun;

import ast.fun, ast.stackframe, ast.scopes, ast.base, ast.variable, ast.pointer, ast.structure, ast.namespace;

class NestedFunction : Function {
  Scope context;
  this(Scope context) {
    this.context = context;
  }
  override string mangleSelf() {
    return context.fun.mangleSelf() ~ "_subfun_" ~ context.fun.mangle(name, type);
  }
  override string mangle(string name, Type type) {
    return mangleSelf() ~ "_" ~ name;
  }
  override int fixup() {
    auto cur = super.fixup();
    add(new Variable(Single!(Pointer, Single!(Void)), "__base_ptr", cur));
    cur += 4;
    return cur;
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
    assert(context);
    if (auto nf = cast(NestedFunction) context.fun) {
      return nf.lookup(name, cast(Expr) nf.lookup("__base_ptr", baseptr));
    } else {
      auto sn = context.lookup(name),
            var = cast(Variable) sn;
      if (!var) return sn;
      assert(baseptr);
      return new MemberAccess_LValue(
        scopeToStruct(context, baseptr),
        var.name
      );
    }
  }
  override Object lookup(string name) { return lookup(name, cast(Expr) lookup("__base_ptr")); }
}

import tools.log;
void callNested(NestedFunction nf, Expr[] params, AsmFile dest) {
  assert(nf.type.ret.size == 4);
  dest.comment("Begin nested call to ", nf);
  params ~= new Register!("ebp");
  foreach_reverse (param; params) {
    dest.comment("Push ", param);
    param.emitAsm(dest);
  }
  dest.put("nestcall "~nf.mangleSelf);
  foreach (param; params) {
    dest.sfree(param.valueType().size);
  }
  if (!cast(Void) nf.type.ret) {
    dest.pushStack("%eax", nf.type.ret);
  }
}

import parseBase;
Object gotNestedFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto sc = cast(Scope) namespace();
  if (!sc) return null;
  auto nf = new NestedFunction(sc);
  if (gotGenericFunDef(nf, text, cont, rest)) {
    return Single!(NoOp);
  }
}
mixin DefaultParser!(gotFunDef, "tree.stmt.nested_fundef");
