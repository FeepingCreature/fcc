module ast.fun;

import ast.namespace, ast.base, ast.scopes, ast.variable, asmfile, ast.types;

class Function : Namespace, Tree {
  string name;
  FunctionType type;
  Scope _scope;
  bool extern_c = false;
  string toString() { return Format("fun ", name, " <- ", sup); }
  // add parameters to namespace
  void fixup() {
    // cdecl: 0 old ebp, 4 return address, 8 parameters .. I think.
    int cur = 8;
    // TODO: alignment
    foreach (param; type.params) {
      if (param._1) {
        add(new Variable(param._0, param._1, cur));
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
  Expr[] params;
  Function fun;
  override void emitAsm(AsmFile af) {
    callFunction(fun, params, af);
  }
  override Type valueType() {
    return fun.type.ret;
  }
}

import tools.log;
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
    dest.pushStack("%eax", fun.type.ret);
  }
}

class FunctionType : Type {
  Type ret;
  Stuple!(Type, string)[] params;
  override int size() { assert(false); }
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
    string toString() { return Format("Function of ", params, " => ", ret); }
  }
}

import parseBase;
Object gotFunDef(ref string text, ParseCb cont, ParseCb rest) {
  Type ptype;
  auto t2 = text;
  Function fun;
  New(fun);
  New(fun.type);
  string parname;
  error = null;
  auto mod = namespace();
  assert(mod);
  if (test(fun.type.ret = cast(Type) rest(t2, "type")) &&
      t2.gotIdentifier(fun.name) &&
      t2.accept("(") &&
      // TODO: function parameters belong on the stackframe
      t2.bjoin(
        test(ptype = cast(Type) rest(t2, "type")) && (t2.gotIdentifier(parname) || ((parname = null), true)),
        t2.accept(","),
        { fun.type.params ~= stuple(ptype, parname); }
      ) &&
      t2.accept(")")
    )
  {
    fun.fixup;
    auto backup = namespace();
    scope(exit) namespace.set(backup); 
    namespace.set(fun);
    mod.add(fun);
    text = t2;
    if (rest(text, "tree.scope", &fun._scope)) return fun;
    else throw new Exception("Couldn't parse function scope at '"~text.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotFunDef, "tree.fundef");

import ast.parse;
Object gotCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Function fun) {
    auto fc = new FunCall;
    fc.fun = fun;
    Expr ex;
    if (t2.accept("(") &&
        t2.bjoin(!!rest(t2, "tree.expr", &ex), t2.accept(","), { fc.params ~= ex; }, false) &&
        t2.accept(")"))
    {
      text = t2;
      return fc;
    }
    else throw new Exception("While parsing arguments for call to "~fun.toString()~": "~t2.next_text());
  };
}
mixin DefaultParser!(gotCallExpr, "tree.rhs_partial.funcall");
