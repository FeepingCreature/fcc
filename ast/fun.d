module ast.fun;

import ast.namespace, ast.base, ast.scopes, ast.variable;

class Function : Namespace, Tree {
  string name;
  FunctionType type;
  Scope _scope;
  bool extern_c = false;
  // declare parameters as variables
  string toString() { return Format("fun ", name, " <- ", sup); }
  void fixup() {
    // cdecl: 0 old ebp, 4 return address, 8 parameters .. I think.
    int cur = 8;
    // TODO: alignment
    foreach (param; type.params) {
      if (param._1) {
        addVar(new Variable(param._0, param._1, cur));
      }
      cur += param._0.size;
    }
  }
  string mangleSelf() {
    if (extern_c || name == "main")
      return name;
    else
      return sup.mangle(name, type);
  }
  override {
    string mangle(string name, Type type) {
      return mangleSelf() ~ "_" ~ name;
    }
    void emitAsm(AsmFile af) {
      af.put(".globl "~mangleSelf);
      af.put(".type "~mangleSelf~", @function");
      af.put(mangleSelf~": ");
      af.put("pushl %ebp");
      af.put("movl %esp, %ebp");
      _scope.emitAsm(af);
      af.put("movl %ebp, %esp");
      af.put("popl %ebp");
      af.put("ret");
    }
  }
}

class FunCall : Expr {
  string name;
  Expr[] params;
  Namespace context;
  override void emitAsm(AsmFile af) {
    callFunction(lookupFun(context, name), params, af);
  }
  override Type valueType() {
    return lookupFun(context, name).type.ret;
  }
}

void callFunction(Function fun, Expr[] params, AsmFile dest) {
  // dest.put("int $3");
  if (params.length) {
    auto p2 = params;
    foreach (entry; fun.type.params)
      entry._0.match(p2);
    assert(!p2.length);
    assert(fun.type.ret.size == 4);
    foreach_reverse (param; params) {
      param.emitAsm(dest);
    }
  } else assert(!fun.type.params.length, Format("Expected ", fun.type.params, "!"));
  dest.put("call "~fun.mangleSelf);
  foreach (param; params) {
    dest.sfree(param.valueType().size);
  }
  if (!cast(Void) fun.type.ret) {
    dest.salloc(fun.type.ret.size);
    dest.mmove4("%eax", "(%esp)");
  }
}

class FunctionType : Type {
  Type ret;
  Stuple!(Type, string)[] params;
  this() { size = -1; } // functions are not values
  override {
    string mangle() {
      string res = "function_to_"~ret.mangle();
      if (!params.length) return res;
      foreach (i, param; params) {
        if (!i) res ~= "_of_";
        else res ~= "_and_";
        res ~= param._0.mangle();
      }
      return res;
    }
  }
}
