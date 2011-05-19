module ast.fun;

import ast.namespace, ast.base, ast.variable, asmfile, ast.types, ast.scopes,
  ast.constant, ast.pointer, ast.literals;

import tools.functional;

// workaround for inability to import ast.modules
interface StoresDebugState {
  bool hasDebug();
}

extern(C) void alignment_emitAligned(Expr ex, AsmFile af);

struct Argument {
  IType type;
  string name;
  Expr initEx;
  int opEquals(Argument other) {
    return name == other.name && type == other.type;
  }
  static Argument opCall(IType it, string name = null, Expr initEx = null) {
    Argument res;
    res.type = it;
    res.name = name;
    res.initEx = initEx;
    return res;
  }
}

class FunSymbol : Symbol {
  Function fun;
  string getName() {
    string res = fun.mangleSelf();
    if (fun.type.stdcall) {
      int size;
      foreach (entry; fun.type.params)
        size += entry.type.size();
      res ~= Format("@", size);
    }
    return res;
  }
  this(Function fun) {
    this.fun = fun;
    super();
  }
  private this() { }
  mixin DefaultDup!();
  string toString() { return Format("symbol<", getName(), ">"); }
  override IType valueType() {
    auto res = new FunctionPointer;
    res.ret = fun.type.ret;
    res.args = fun.type.params;
    res.args ~= Argument(Single!(SysInt));
    res.stdcall = fun.type.stdcall;
    return res;
  }
}

extern(C) Object nf_fixup__(Object obj, Expr mybase);

class Function : Namespace, Tree, Named, SelfAdding, IsMangled, FrameRoot, Extensible {
  string name;
  Expr getPointer() {
    return new FunSymbol(this);
  }
  FunctionType type;
  Tree tree;
  bool extern_c = false, weak = false;
  void markWeak() { weak = true; }
  mixin defaultIterate!(tree);
  // iterate the compound expressions that form this function
  void iterateExpressions(void delegate(ref Iterable) dg) { }
  string toString() { return Format("fun ", name, " ", type, " <- ", sup); }
  // add parameters to namespace
  int _framestart;
  Function alloc() { return new Function; }
  Argument[] getParams() { return type.params; }
  Function flatdup() { // NEVER dup the tree!
    auto res = alloc();
    res.name = name;
    res.type = type;
    res.weak = weak;
    res.extern_c = extern_c;
    res.tree = tree;
    res._framestart = _framestart;
    res.sup = sup;
    res.field = field;
    res.rebuildCache;
    return res;
  }
  Function dup() {
    auto res = flatdup();
    if (tree) res.tree = tree.dup;
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
      _framestart += param.type.size;
      add(new Variable(param.type, param.name, cur));
      cur += param.type.size;
    }
    return cur;
  }
  string cleaned_name() { return name.cleanup(); }
  override string mangleSelf() {
    if (extern_c) {
      auto res = cleaned_name;
      if (platform_prefix == "i686-mingw32-") {
        res = "_"~res;
        if (res == "_setjmp") res = "__setjmp"; // lol wat.
      }
      return res;
    } else if (name == "__c_main") {
      return "main";
    } else if (name == "__win_main") {
      if (platform_prefix == "i686-mingw32-") {
        return "_WinMain@16";
      } else return "_WinMain_not_relevant_on_this_architecture";
    } else
      return sup.mangle(cleaned_name, type);
  }
  string exit() { return mangleSelf() ~ "_exit_label"; }
  static int funid_count;
  override {
    int framestart() { return _framestart; }
    bool addsSelf() { return true; }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      auto fmn = mangleSelf(); // full mangled name
      af.put(".p2align 4");
      af.put(".globl ", fmn);
      if (!isWindoze()) // TODO: work out why win32 gas does not like this
        af.put(".type ", fmn, ", @function");
      if (weak) af.put(".weak ", fmn);
      af.put(fmn, ":"); // not really a label
      auto idnum = funid_count ++;
      af.put(".LFB", idnum, ":");
      af.jump_barrier();
      // af.put(".cfi_startproc");
      
      af.pushStack("%ebp", nativePtrSize);
      af.mmove4("%esp", "%ebp");
      if (af.profileMode)
        af.put("call mcount");
      
      auto backup = af.currentStackDepth;
      scope(exit) af.currentStackDepth = backup;
      af.currentStackDepth = 0;
      withTLS(namespace, this, tree.emitAsm(af));
      af.emitLabel(exit(), true);
      
      // af.mmove4("%ebp", "%esp");
      // af.popStack("%ebp", nativePtrSize);
      af.put("leave");
      
      af.jump_barrier();
      af.put("ret");
      af.put(".LFE", idnum, ":");
      if (!isWindoze())
        af.put(".size ", fmn, ", .-", fmn);
      // af.put(".cfi_endproc");
    }
    Stuple!(IType, string, int)[] stackframe() {
      Stuple!(IType, string, int)[] res;
      foreach (obj; field)
        if (auto var = fastcast!(Variable)~ obj._1)
          res ~= stuple(var.type, var.name, var.baseOffset);
      return res;
    }
  }
  override Object lookup(string name, bool local = false) {
    return super.lookup(name, local);
  }
  override Object extend(Object obj2) {
    auto fun2 = fastcast!(Function) (obj2);
    if (!fun2)
      throw new Exception(Format("Can't overload function "
        "with non-function: ", this, " with ", obj2, "!"
      ));
    auto set = new OverloadSet(name, this, fun2);
    return set;
  }
}

class OverloadSet : Named, Extensible {
  string name;
  Function[] funs;
  this(string n, Function[] f...) {
    name = n; funs = f.dup;
  }
  private this() { }
  override string getIdentifier() { return name; }
  override Object extend(Object obj2) {
    auto fun2 = fastcast!(Function) (obj2);
    if (!fun2)
      throw new Exception(Format("Can't overload '", name,
        "' with non-function ", obj2, "!"
      ));
    auto res = new OverloadSet;
    res.name = name;
    res.funs = funs.dup ~ fun2;
    return res;
  }
}

class FunCall : Expr {
  Expr[] params;
  Function fun;
  Expr[] getParams() { return params; }
  FunCall dup() {
    auto res = new FunCall;
    res.fun = fun.flatdup();
    
    foreach (param; params) res.params ~= param.dup;
    return res;
  }
  void iterate(void delegate(ref Iterable) dg) {
    fun.iterateExpressions(dg);
    defaultIterate!(params).iterate(dg);
  }
  void emitWithArgs(AsmFile af, Expr[] args) {
    auto size = (fun.type.ret == Single!(Void))?0:fun.type.ret.size;
    mixin(mustOffset("size"));
    callFunction(af, fun.type.ret, fun.extern_c, fun.type.stdcall, args, fun.getPointer());
  }
  override void emitAsm(AsmFile af) {
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
      af.pushStack("%edx", 4);
      af.nvm("%edx");
    }
    if (ret.size >= 12) {
      af.pushStack("%ecx", 4);
      af.nvm("%ecx");
    }
    if (ret.size == 16) {
      af.pushStack("%ebx", 4);
      af.nvm("%ebx");
    }
    if (ret.size >= 4) {
      af.pushStack("%eax", 4);
      af.nvm("%eax");
    } else if (ret.size == 2) {
      af.pushStack("%ax", 2);
      af.nvm("%ax");
    } else if (ret.size == 1) {
      af.pushStack("%al", 1);
      af.nvm("%al");
    }
  }
}

import tools.log;
void callFunction(AsmFile af, IType ret, bool external, bool stdcall, Expr[] params, Expr fp) {
  if (!ret) throw new Exception("Tried to call function but return type not yet known! ");
  {
    mixin(mustOffset("0", "outer"));
    string name;
    if (auto s = fastcast!(Symbol) (fp)) name = s.getName();
    else name = "(nil)";
    
    ret = resolveType(ret);
    assert(ret.size == 1 /or/ 2 /or/ 4 /or/ 8 /or/ 12 /or/ 16 || cast(Void) ret,
      Format("Return bug: ", ret, " from ", name, ": ",
      ret.size, " is ", (fastcast!(Object)~ ret).classinfo.name));
    af.comment("Begin call to ", name);
    
    bool backupESI = external && name != "setjmp";
    
    if (backupESI) af.pushStack("%esi", nativePtrSize);
    
    int paramsize;
    foreach (param; params) paramsize += param.valueType().size;
    paramsize += af.floatStackDepth * 8;
    paramsize += 8; // push ip, push ebp
    
    auto alignCall = 16 - (af.currentStackDepth + paramsize) % 16;
    if (alignCall == 16) alignCall = 0;
    af.salloc(alignCall);
    
    auto restore = af.floatStackDepth;
    while (af.floatStackDepth)
      af.fpuToStack();
    
    {
      mixin(mustOffset("0", "innerer"));
      foreach_reverse (param; params) {
        // af.comment("Push ", param);
        alignment_emitAligned(param, af);
      }
      
      {
        mixin(mustOffset("nativePtrSize", "innerest"));
        if (fp.valueType().size > nativePtrSize) asm { int 3; }
        fp.emitAsm(af);
      }
      af.popStack("%eax", 4);
      
      af.call("%eax");
      
      foreach (param; params) {
        if (param.valueType() != Single!(Void)) {
          if (stdcall) {
            af.currentStackDepth -= param.valueType().size;
          } else {
            af.sfree(param.valueType().size);
          }
        }
      }
    }
    
    if (ret == Single!(Float) || ret == Single!(Double))
      af.floatStackDepth ++;
    
    while (restore--) {
      af.stackToFpu();
      if (ret == Single!(Float) || ret == Single!(Double))
        af.swapFloats;
    }
    af.sfree(alignCall);
    
    if (backupESI) af.popStack("%esi", nativePtrSize);
  }
  
  auto size = (ret == Single!(Void))?0:ret.size;
  mixin(mustOffset("size"));
  handleReturn(ret, af);
}

class FunctionType : ast.types.Type {
  IType ret;
  Argument[] params;
  bool stdcall;
  override int size() {
    asm { int 3; }
    assert(false);
  }
  IType[] types() {
    auto res = new IType[params.length];
    foreach (i, entry; params) res[i] = entry.type;
    return res;
  }
  override {
    string mangle() {
      string res = "function_to_"~ret.mangle();
      if (!params.length) return res;
      foreach (i, param; params) {
        if (!i) res ~= "_of_";
        else res ~= "_and_";
        res ~= param.type.mangle();
      }
      return res;
    }
    string toString() { return Format("Function of ", params, " => ", ret); }
  }
}

bool gotParlist(ref string str, ref Argument[] res, ParseCb rest) {
  auto t2 = str;
  IType ptype, lastType;
  string parname;
  Expr init;
  bool gotInitializer(ref string text, out Expr res) {
    auto t2 = text;
    if (!t2.accept("=")) return false;
    if (!rest(t2, "tree.expr", &res))
      return false;
    text = t2;
    return true;
  }
  if (t2.accept("(") &&
      t2.bjoin(
        ( // can omit types for subsequent parameters
          test(ptype = fastcast!(IType)~ rest(t2, "type")) || test(ptype = lastType)
        ) && (
          t2.gotIdentifier(parname) || ((parname = null), true)
        ) && (
          gotInitializer(t2, init) || ((init = null), true)
        ),
        t2.accept(","),
        { lastType = ptype; res ~= Argument(ptype, parname, init); }
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
Object gotGenericFun(T, bool Decl)(T _fun, Namespace sup_override, bool addToNamespace,
                           ref string text, ParseCb cont, ParseCb rest, string forcename = null) {
  IType ptype;
  auto t2 = text;
  string parname;
  *error.ptr() = stuple("", "");
  auto ns = namespace();
  assert(!!ns);
  
  IType ret;
  string fun_name;
  Argument[] _params;
  string t3 = t2;
  if
    (
      (
        (test(ret = fastcast!(IType) (rest(t3, "type"))) && (t2 = t3, true))
        ||
        t2.accept("auto")
      )
      &&
      (
        forcename || t2.gotIdentifier(fun_name)
      )
      &&
      t2.gotParlist(_params, rest)
    )
  {
    static if (is(typeof(_fun()))) auto fun = _fun();
    else auto fun = _fun;
    New(fun.type);
    fun.type.ret = ret;
    fun.type.params = _params;
    fun.name = forcename?forcename:fun_name;
    fun.sup = sup_override ? sup_override : ns;
    
    auto backup = namespace();
    namespace.set(fun);
    scope(exit) namespace.set(backup);
    
    if (fun.name == "main") {
      if (gotMain) {
        t2.failparse("Main already defined! ");
      }
      gotMain = fun;
      fun.name = "__fcc_main";
    }
    fun.fixup;
    if (addToNamespace) { fun.sup = null; ns.add(fun); if (!fun.sup) { logln("FAIL under ", ns, "! "); asm { int 3; } } }
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
  Argument[] args;
  bool stdcall;
  this() { }
  string toString() { return Format(ret, " function(", args, ")"); }
  this(IType ret, Argument[] args) {
    this.ret = ret;
    this.args = args.dup;
  }
  this(Function fun) {
    ret = fun.type.ret;
    args = fun.type.params.dup;
  }
  override int size() {
    return nativePtrSize;
  }
  override string mangle() {
    auto res = "fp_ret_"~ret.mangle()~"_args";
    if (!args.length) res ~= "_none";
    else foreach (arg; args)
      res ~= "_"~arg.type.mangle();
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
    Argument[] list;
    auto t2 = text;
    if (t2.accept("function") &&
      t2.gotParlist(list, rest)
    ) {
      text = t2;
      auto res = new FunctionPointer;
      res.ret = cur;
      res.args = list.dup;
      return res;
    } else return null;
  };
}
