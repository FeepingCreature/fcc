module ast.fun;

import ast.namespace, ast.base, ast.variable, asmfile, ast.types, ast.scopes,
  ast.constant, ast.pointer, ast.literals;

import tools.functional;

// workaround for inability to import ast.modules
interface StoresDebugState {
  bool hasDebug();
}

class FunSymbol : Symbol {
  Function fun;
  this(Function fun) {
    this.fun = fun;
    super(fun.mangleSelf());
  }
  private this() { }
  mixin DefaultDup!();
  string toString() { return Format("symbol<", name, ">"); }
  override IType valueType() {
    auto res = new FunctionPointer;
    res.ret = fun.type.ret;
    res.args = fun.type.params /map/ ex!("a, b -> a");
    res.args ~= Single!(SysInt);
    return res;
  }
}

extern(C) Object nf_fixup__(Object obj, Expr mybase);

class Function : Namespace, Tree, Named, SelfAdding, IsMangled, FrameRoot {
  string name;
  Expr getPointer() {
    return new FunSymbol(this);
  }
  FunctionType type;
  Tree tree;
  bool extern_c = false;
  mixin defaultIterate!(tree);
  string toString() { return Format("fun ", name, " ", type, " <- ", sup); }
  // add parameters to namespace
  int _framestart;
  Function alloc() { return new Function; }
  IType[] getParamTypes() { return type.types(); }
  Function dup() {
    auto res = alloc();
    res.name = name;
    res.type = type;
    res.extern_c = extern_c;
    res.tree = tree.dup;
    res._framestart = _framestart;
    res.sup = sup;
    res.field = field;
    res.rebuildCache;
    return res;
  }
  FunCall mkCall() {
    auto res = new FunCall;
    res.fun = this;
    return res;
  }
  int fixup() {
    // cdecl: 0 old ebp, 4 return address, 8 parameters .. I think.
    add(new Variable(Single!(SizeT), "__old_ebp", 0));
    add(new Variable(Single!(SizeT), "__fun_ret", 4));
    int cur = _framestart = 8;
    // TODO: alignment
    foreach (param; type.params) {
      // if (param._1) { // what the HELL
        _framestart += param._0.size;
        add(new Variable(param._0, param._1, cur));
      // }
      cur += param._0.size;
    }
    return cur;
  }
  string cleaned_name() { return name.cleanup(); }
  override string mangleSelf() {
    if (extern_c)
      return cleaned_name;
    else if (name == "_c_main")
      return "main";
    else
      return sup.mangle(cleaned_name, type);
  }
  string exit() { return mangleSelf() ~ "_exit_label"; }
  override {
    int framestart() { return _framestart; }
    bool addsSelf() { return true; }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      auto fmn = mangleSelf(); // full mangled name
      af.put(".globl ", fmn);
      af.put(".type ", fmn, ", @function");
      af.put(fmn, ":"); // not really a label
      af.jump_barrier();
      
      af.pushStack("%ebp", voidp);
      af.mmove4("%esp", "%ebp");
      
      auto backup = af.currentStackDepth;
      scope(exit) af.currentStackDepth = backup;
      af.currentStackDepth = 0;
      withTLS(namespace, this, tree.emitAsm(af));
      af.emitLabel(exit());
      
      af.mmove4("%ebp", "%esp");
      af.popStack("%ebp", voidp);
      
      af.jump_barrier();
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
  override Object lookup(string name, bool local = false) {
    return super.lookup(name, local);
  }
}

class FunCall : Expr {
  Expr[] params;
  Function fun;
  FunCall dup() {
    auto res = new FunCall;
    res.fun = fun;
    foreach (param; params) res.params ~= param.dup;
    return res;
  }
  mixin defaultIterate!(params);
  void emitWithArgs(AsmFile af, Expr[] args) {
    auto size = (fun.type.ret == Single!(Void))?0:fun.type.ret.size;
    mixin(mustOffset("size"));
    callFunction(af, fun.type.ret, args, fun.getPointer());
  }
  override void emitAsm(AsmFile af) {
    if (fun.name == "_fcc_main")
      dontAlignThis = true;
    emitWithArgs(af, params);
  }
  override string toString() { return Format("call(", fun, params, ")"); }
  override IType valueType() {
    return fun.type.ret;
  }
}

void handleReturn(IType ret, AsmFile af) {
  if (Single!(Float) == ret) {
    af.salloc(4);
    af.storeFloat("(%esp)");
    return;
  }
  if (Single!(Double) == ret) {
    af.salloc(8);
    af.storeDouble("(%esp)");
    return;
  }
  if (ret != Single!(Void)) {
    if (ret.size >= 8) {
      af.pushStack("%edx", Single!(SizeT));
      af.nvm("%edx");
    }
    if (ret.size >= 12) {
      af.pushStack("%ecx", Single!(SizeT));
      af.nvm("%ecx");
    }
    if (ret.size == 16) {
      af.pushStack("%ebx", Single!(SizeT));
      af.nvm("%ebx");
    }
    if (ret.size >= 4) {
      af.pushStack("%eax", Single!(SizeT));
      af.nvm("%eax");
    } else if (ret.size == 2) {
      af.pushStack("%ax", Single!(Short));
      af.nvm("%ax");
    }
  }
}

import tools.log;
bool dontAlignThis;
void callFunction(AsmFile af, IType ret, Expr[] params, Expr fp) {
  // af.put("int $3");
  {
    mixin(mustOffset("0", "outer"));
    string name;
    if (auto s = cast(Symbol) fp) name = s.name;
    else name = "(nil)";
    
    ret = resolveType(ret);
    assert(ret.size == 2 /or/ 4 /or/ 8 /or/ 12 /or/ 16 || cast(Void) ret,
      Format("Return bug: ", ret, " from ", name, ": ",
      ret.size, " is ", (cast(Object) ret).classinfo.name));
    af.comment("Begin call to ", name);
    
    int paramsize;
    foreach (param; params) paramsize += param.valueType().size;
    paramsize += af.floatStackDepth * 8;
    paramsize += 8; // push ip, push ebp
    
    auto alignCall = 16 - (af.currentStackDepth + paramsize) % 16;
    if (alignCall == 16) alignCall = 0;
    if (!dontAlignThis)
      af.salloc(alignCall);
    
    auto restore = af.floatStackDepth;
    while (af.floatStackDepth)
      af.fpuToStack();
    
    {
      mixin(mustOffset("0", "innerer"));
      foreach_reverse (param; params) {
        af.comment("Push ", param);
        param.emitAsm(af);
      }
      
      {
        mixin(mustOffset("nativePtrSize", "innerest"));
        if (fp.valueType().size > nativePtrSize) asm { int 3; }
        fp.emitAsm(af);
      }
      af.popStack("%eax", Single!(SizeT));
      
      af.call("%eax");
      
      foreach (param; params) {
        if (param.valueType() != Single!(Void))
          af.sfree(param.valueType().size);
      }
    }
    
    if (ret == Single!(Float) || ret == Single!(Double))
      af.floatStackDepth ++;
    
    while (restore--) {
      af.stackToFpu();
      if (ret == Single!(Float) || ret == Single!(Double))
        af.swapFloats;
    }
    if (dontAlignThis) dontAlignThis = false;
    else af.sfree(alignCall);
  }
  
  auto size = (ret == Single!(Void))?0:ret.size;
  mixin(mustOffset("size"));
  handleReturn(ret, af);
}

class FunctionType : ast.types.Type {
  IType ret;
  Stuple!(IType, string)[] params;
  override int size() {
    asm { int 3; }
    assert(false);
  }
  IType[] types() {
    auto res = new IType[params.length];
    foreach (i, entry; params) res[i] = entry._0;
    return res;
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
  IType ptype, lastType;
  string parname;
  if (t2.accept("(") &&
      t2.bjoin(
        ( // can omit types for subsequent parameters
          test(ptype = cast(IType) rest(t2, "type")) || test(ptype = lastType)
        ) && (t2.gotIdentifier(parname) || ((parname = null), true)),
        t2.accept(","),
        { lastType = ptype; res ~= stuple(ptype, parname); }
      ) &&
      t2.accept(")")
  ) {
    str = t2;
    return true;
  } else {
    return false;
  }
}

Function gotMain;

import parseBase;
// generalized to reuse for nested funs
Object gotGenericFun(T, bool Decl)(T fun, Namespace sup_override, bool addToNamespace,
                           ref string text, ParseCb cont, ParseCb rest, string forcename = null) {
  IType ptype;
  auto t2 = text;
  New(fun.type);
  string parname;
  *error.ptr() = stuple("", "");
  auto ns = namespace();
  assert(!!ns);
  if (test(fun.type.ret = cast(IType) rest(t2, "type")) &&
      (forcename || t2.gotIdentifier(fun.name)) &&
      t2.gotParlist(fun.type.params, rest)
    )
  {
    if (forcename) fun.name = forcename;
    if (fun.name == "main") {
      assert(!gotMain);
      gotMain = fun;
      fun.name = "_fcc_main";
    }
    fun.fixup;
    auto backup = ns;
    scope(exit) namespace.set(backup);
    namespace.set(fun);
    if (addToNamespace) ns.add(fun);
    fun.sup = sup_override?sup_override:ns;
    text = t2;
    static if (Decl) {
      if (text.accept(";")) return fun;
      else t2.failparse("Expected ';'");
    } else {
      if (rest(text, "tree.scope", &fun.tree)) {
        // TODO: Reserve "sys" module name
        return fun;
      } else text.failparse("Couldn't parse function scope");
    }
  } else return null;
}

Object gotGenericFunDef(T)(T fun, Namespace sup_override, bool addToNamespace, ref string text, ParseCb cont, ParseCb rest, string forcename = null) {
  return gotGenericFun!(T, false)(fun, sup_override, addToNamespace, text, cont, rest, forcename);
}
Object gotGenericFunDecl(T)(T fun, Namespace sup_override, bool addToNamespace, ref string text, ParseCb cont, ParseCb rest, string forcename = null) {
  return gotGenericFun!(T, true)(fun, sup_override, addToNamespace, text, cont, rest, forcename);
}

Object gotFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto fun = new Function;
  return gotGenericFunDef(fun, cast(Namespace) null, true, text, cont, rest);
}
mixin DefaultParser!(gotFunDef, "tree.fundef");

// ensuing code gleefully copypasted from nestfun
// yes I wrote delegates first. how about that.
class FunctionPointer : ast.types.Type {
  IType ret;
  IType[] args;
  this() { }
  string toString() { return Format(ret, " function(", args, ")"); }
  this(IType ret, IType[] args) {
    this.ret = ret;
    this.args = args.dup;
  }
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

// &fun
class FunRefExpr : Expr, Literal {
  Function fun;
  this(Function fun) { this.fun = fun; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override {
    IType valueType() {
      return new FunctionPointer(fun);
    }
    void emitAsm(AsmFile af) {
      (new Constant(fun.mangleSelf())).emitAsm(af);
    }
    string getValue() { return fun.mangleSelf(); }
  }
}

import ast.casting;
Object gotFunRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  Function fun;
  if (!rest(text, "tree.expr _tree.expr.arith", &fun))
    return null;
  
  return new FunRefExpr(fun);
}
mixin DefaultParser!(gotFunRefExpr, "tree.expr.fun_ref", "2101", "&");

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
