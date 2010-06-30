module ast.fun;

import ast.namespace, ast.base, ast.scopes, ast.variable, asmfile, ast.types,
  ast.constant;

class Function : Namespace, Tree {
  string name;
  FunctionType type;
  Scope _scope;
  bool extern_c = false;
  mixin defaultIterate!(_scope);
  string toString() { return Format("fun ", name, " <- ", sup); }
  // add parameters to namespace
  int _framestart;
  FunCall mkCall() { return new FunCall; }
  int fixup() {
    // cdecl: 0 old ebp, 4 return address, 8 parameters .. I think.
    add(new Variable(Single!(SizeT), "__old_ebp", 0));
    add(new Variable(Single!(SizeT), "__fun_ret", 4));
    int cur = _framestart = 8;
    // TODO: alignment
    foreach (param; type.params) {
      if (param._1) {
        _framestart += param._0.size;
        add(new Variable(param._0, param._1, cur));
      }
      cur += param._0.size;
    }
    return cur;
  }
  string mangleSelf() {
    if (extern_c || name == "main")
      return name;
    else
      return sup.mangle(name, type);
  }
  int framestart() {
    return _framestart;
  }
  override {
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    void emitAsm(AsmFile af) {
      af.put(".globl "~mangleSelf);
      af.put(".type "~mangleSelf~", @function");
      af.put(mangleSelf~": ");
      af.put("pushl %ebp");
      af.put("movl %esp, %ebp");
      withTLS(namespace, this, _scope.emitAsm(af));
      af.put("movl %ebp, %esp");
      af.put("popl %ebp");
      af.put("ret");
    }
    Stuple!(IType, string, int)[] stackframe() {
      Stuple!(IType, string, int)[] res;
      foreach (obj; field)
        if (auto var = cast(Variable) obj._1)
          res ~= stuple(var.type, var.name, var.baseOffset);
      return res;
    }
  }
}

class FunCall : Expr {
  Expr[] params;
  Function fun;
  mixin defaultIterate!(params);
  override void emitAsm(AsmFile af) {
    callFunction(af, fun.type.ret, params, fun.mangleSelf());
  }
  override IType valueType() {
    return fun.type.ret;
  }
}

import tools.log;
void callFunction(AsmFile dest, IType ret, Expr[] params, string name, Expr fp = null) {
  // dest.put("int $3");
  assert(ret.size == 4 || cast(Void) ret, Format("Return bug: ", ret, " from ", name, "!"));
  dest.comment("Begin call to ", name);
  if (params.length) {
    foreach_reverse (param; params) {
      dest.comment("Push ", param);
      param.emitAsm(dest);
    }
  }
  if (fp) {
    fp.emitAsm(dest);
    dest.popStack("%eax", Single!(SizeT));
    dest.put("call *%eax");
  } else {
    dest.put("call "~name);
  }
  foreach (param; params) {
    dest.sfree(param.valueType().size);
  }
  if (!cast(Void) ret) {
    dest.pushStack("%eax", ret);
  }
}

class FunctionType : Type {
  IType ret;
  Stuple!(IType, string)[] params;
  override int size() {
    asm { int 3; }
    assert(false);
  }
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

bool gotParlist(ref string str, ref Stuple!(IType, string)[] res, ParseCb rest) {
  auto t2 = str;
  IType ptype;
  string parname;
  if (t2.accept("(") &&
      t2.bjoin(
        test(ptype = cast(IType) rest(t2, "type")) && (t2.gotIdentifier(parname) || ((parname = null), true)),
        t2.accept(","),
        { res ~= stuple(ptype, parname); }
      ) &&
      t2.accept(")")
  ) {
    str = t2;
    return true;
  } else return false;
}

import parseBase;
// generalized to reuse for nested funs
Object gotGenericFunDef(T)(T fun, Namespace sup_override, ref string text, ParseCb cont, ParseCb rest) {
  IType ptype;
  auto t2 = text;
  New(fun.type);
  string parname;
  error = null;
  auto ns = namespace();
  assert(ns);
  if (test(fun.type.ret = cast(IType) rest(t2, "type")) &&
      t2.gotIdentifier(fun.name) &&
      t2.gotParlist(fun.type.params, rest)
    )
  {
    fun.fixup;
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(fun);
    ns.add(fun);
    fun.sup = sup_override?sup_override:ns;
    text = t2;
    if (rest(text, "tree.scope", &fun._scope)) return fun;
    else throw new Exception("Couldn't parse function scope at '"~text.next_text()~"'");
  } else return null;
}

Object gotFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto fun = new Function;
  return gotGenericFunDef(fun, cast(Namespace) null, text, cont, rest);
}

mixin DefaultParser!(gotFunDef, "tree.fundef");

Expr[] matchCall(ref string text, string info, IType[] params, ParseCb rest) {
  Expr[] res;
  auto t2 = text;
  int param_offset;
  Expr ex;
  if (t2.bjoin(
    !!rest(t2, "tree.expr", &ex, (Expr ex) {
      if (param_offset !< params.length)
        throw new Exception(Format(
          "Extraneous parameter for ", info, ": ", ex
        ));
      if (cast(Variadic) params[param_offset]) {
        // why are you using static arrays as parameters anyway?
        return !cast(StaticArray) ex.valueType();
      } else {
        // logln("Try ", ex.valueType(), " into ", fun.type.params[param_offset]._0);
        if (ex.valueType() != cast(Object) params[param_offset])
          // TODO: set error
          return false;
        param_offset ++;
        return true;
      }
    }),
    t2.accept(","),
    { res ~= ex; },
    true
  )) {
    if (params.length && cast(Variadic) params[$-1]) {
      param_offset ++;
    }
    
    if (param_offset < params.length) {
      throw new Exception(Format(
        "Not enough parameters for ", info, ": ",
        res, " at ", t2.next_text(), "!"
      ));
    }
    
    if (!t2.accept(")")) {
      throw new Exception(Format(
        "Unidentified text in call to ", info, ": ",
        "'", t2.next_text(), "'"
      ));
    }
    
    text = t2;
    
    return res;
  } else return null;
}

import ast.parse, ast.static_arrays;
Object gotCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Function fun) {
    auto fc = fun.mkCall();
    fc.fun = fun;
    
    if (t2.accept("(")) {
      scope params = new IType[fun.type.params.length];
      foreach (i, ref p; params) p = fun.type.params[i]._0;
      fc.params = matchCall(t2, fun.name, params, rest);
      text = t2;
      return fc;
    }
    else throw new Exception("While parsing arguments for call to "~fun.toString()~": "~t2.next_text());
  };
}
mixin DefaultParser!(gotCallExpr, "tree.rhs_partial.funcall", null, true);

// ensuing code gleefully copypasted from nestfun
// yes I wrote delegates first. how about that.
class FunctionPointer : Type {
  IType ret;
  IType[] args;
  this() { }
  this(Function fun) {
    ret = fun.type.ret;
    foreach (p; fun.type.params)
      args ~= p._0;
  }
  override int size() {
    return nativePtrSize;
  }
  override string mangle() {
    auto res = "fp_ret_"~ret.mangle()~"_args";
    if (!args.length) res ~= "_none";
    else foreach (arg; args)
      res ~= "_"~arg.mangle();
    return res;
  }
}

class FpCall : Expr {
  Expr fp;
  Expr[] params;
  mixin defaultIterate!(params);
  override void emitAsm(AsmFile af) {
    auto fntype = cast(FunctionPointer) fp.valueType();
    callFunction(af, fntype.ret, params, "fp", fp);
  }
  override IType valueType() {
    return (cast(FunctionPointer) fp.valueType()).ret;
  }
}

Object gotFpCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Expr ex) {
    auto fptype = cast(FunctionPointer) ex.valueType();
    if (!fptype) return null;
    
    auto fc = new FpCall;
    fc.fp = ex;
    
    if (t2.accept("(")) {
      fc.params = matchCall(t2, Format("delegate ", ex), fptype.args, rest);
      text = t2;
      return fc;
    } else return null;
  };
}
mixin DefaultParser!(gotFpCallExpr, "tree.rhs_partial.fpcall", null, true);

// &fun
class FunRefExpr : Expr {
  Function fun;
  this(Function fun) { this.fun = fun; }
  mixin defaultIterate!();
  override {
    IType valueType() {
      return new FunctionPointer(fun);
    }
    void emitAsm(AsmFile af) {
      (new Constant(fun.mangleSelf())).emitAsm(af);
    }
  }
}

Object gotFunRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("&")) return null;
  
  string ident;
  if (!t2.gotIdentifier(ident, true)) return null;
  auto fun = cast(Function) namespace().lookup(ident);
  if (!fun) return null;
  
  text = t2;
  
  return new FunRefExpr(fun);
}
mixin DefaultParser!(gotFunRefExpr, "tree.expr.fun_ref", "2101");

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb rest) {
    IType ptype;
    Stuple!(IType, string)[] list;
    auto t2 = text;
    if (t2.accept("function") &&
      t2.gotParlist(list, rest)
    ) {
      text = t2;
      auto res = new FunctionPointer;
      res.ret = cur;
      foreach (entry; list) res.args ~= entry._0;
      return res;
    } else return null;
  };
}
