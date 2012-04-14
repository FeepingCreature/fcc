module ast.fun;

import ast.namespace, ast.base, ast.variable, asmfile, ast.types, ast.scopes,
  ast.constant, ast.pointer, ast.literals, ast.vardecl, ast.assign;

import tools.functional;
import dwarf2;

// workaround for inability to import ast.modules
interface StoresDebugState {
  bool hasDebug();
}

extern(C) void alignment_emitAligned(Expr ex, AsmFile af);

alias asmfile.startsWith startsWith;

struct Argument {
  IType type;
  string name;
  Expr initEx;
  int opEquals(Argument other) {
    return name == other.name && type == other.type;
  }
  string toString() { return qformat(type, " ", name); }
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
  string toString() { return Format("symbol<", fun, ">"); }
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

extern(C) void funcall_emit_fun_end_guard(AsmFile af, string name);

bool[string] symbol_emit_win32_hack_check;
Object hack_sync;
static this() { hack_sync = new Object; }

class Function : Namespace, Tree, Named, SelfAdding, IsMangled, FrameRoot, Extensible, ScopeLike, EmittingContext, Importer {
  string name;
  Expr getPointer() {
    return new FunSymbol(this);
  }
  FunctionType type;
  Tree tree;
  bool extern_c = false, weak = false, reassign = false, isabstract = false;
  void markWeak() { weak = true; }
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    if (mode == IterMode.Lexical) { parseMe; defaultIterate!(tree).iterate(dg, mode); }
    // else to be defined in subclasses
  }
  string toString() { return Format("fun ", name, " ", type, " <- ", sup); }
  // add parameters to namespace
  int _framestart;
  string coarseSrc;
  Namespace coarseContext;
  IModule coarseModule;
  bool inEmitAsm;
  mixin ImporterImpl!();
  override bool isBeingEmat() { return inEmitAsm; }
  void parseMe() {
    if (!coarseSrc) return;
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(coarseContext);
    if (tree) namespace.set(fastcast!(Scope) (tree));
    
    // No! Bad! Wrong!
    // auto backupmod = current_module();
    // scope(exit) current_module.set(backupmod);
    // current_module.set(coarseModule);
    
    // logln("parse function ", name, " in ", coarseContext, ": ", coarseSrc.ptr);
    
    // needed because we may be a template function (!)
    pushCache();
    scope(exit) popCache();
    
    string t2 = coarseSrc;
    auto stmt = fastcast!(Statement) (parsecon.parse(t2, "tree.scope"));
    if (!stmt) {
      // fail();
      t2.failparse("Couldn't parse function scope");
    }
    addStatement(stmt);
    opt(tree);
    t2 = t2.mystripl();
    if (t2.length)
      t2.failparse("Unknown text! ");
    coarseSrc = null;
  }
  Function alloc() { return new Function; }
  Argument[] getParams() { return type.params; }
  Function flatdup() { // NEVER dup the tree!
    auto res = alloc();
    res.name = name;
    res.type = type;
    res.weak = weak;
    res.extern_c = extern_c;
    res.tree = tree;
    res.coarseSrc = coarseSrc;
    res.coarseContext = coarseContext;
    res.coarseModule = coarseModule;
    res._framestart = _framestart;
    res.sup = sup;
    res.field = field;
    res.rebuildCache;
    return res;
  }
  Function dup() {
    auto res = flatdup();
    if (tree) res.tree = tree.dup;
    res.coarseSrc = coarseSrc;
    return res;
  }
  FunCall mkCall() {
    auto res = new FunCall;
    res.fun = this;
    return res;
  }
  int fixup() {
    // cdecl: 0 old ebp, 4 return address, 8 parameters
    int cur;
    if (isARM) {
      add(new Variable(Single!(SizeT), "__old_ebp", -4));
      add(new Variable(Single!(SizeT), "__fun_ret", 0));
      cur = _framestart = 4;
    } else {
      add(new Variable(Single!(SizeT), "__old_ebp", 0));
      add(new Variable(Single!(SizeT), "__fun_ret", 4));
      cur = _framestart = 8;
    }
    // TODO: 16-byte? alignment
    foreach (param; type.params) {
      auto pt = param.type;
      _framestart += pt.size;
      add(new Variable(pt, param.name, cur));
      cur += pt.size;
      cur = (cur + 3) & ~3; // round to 4
    }
    if (!releaseMode) {
      if (tree) {
        logln(tree);
        fail;
      }
      /*auto sysmod = __getSysmod();
      if (!extern_c && name != "main2"[] /or/ "__win_main"[] /or/ "__c_main"[] && !tools.base.startsWith(name, "guardfn_") && sysmod && sysmod.lookup("FrameInfo")) {
        auto type = fastcast!(IType) (sysmod.lookup("FrameInfo"));
        auto var = new Variable(type, "__frame_info", boffs(type));
        var.initInit;
        auto decl = new VarDecl(var);
        addStatement(decl);
        auto sc = fastcast!(Scope) (tree);
        namespace.set(sc);
        if (auto mistake = sc.lookup("__frame_info", true)) {
          logln(mistake, " in ", sc, " ", sc.field, ": wtf");
          fail;
        }
        sc.add(var);
        auto stackframe_var = fastcast!(Expr) (sysmod.lookup("stackframe"));
        auto vartype = fastcast!(RelNamespace)(var.valueType());
        addStatement(mkAssignment(fastcast!(Expr) (vartype.lookupRel("fun", var)), mkString(fqn())));
        addStatement(mkAssignment(fastcast!(Expr) (vartype.lookupRel("prev", var)), stackframe_var));
        addStatement(mkAssignment(stackframe_var, new RefExpr(var)));
        addStatement(iparse!(Statement, "frame_guard", "tree.stmt.guard")
                            (`onExit { sf = sf.prev; } `, namespace(), "sf", stackframe_var));
      }*/
    }
    return cur;
  }
  string cleaned_name() { return name.cleanup(); }
  string pretty_name() {
    auto mod = get!(IModule).modname();
    auto res = Format(type.ret, " ", mod, ".", name);
    res ~= "(";
    foreach (i, arg; type.params) {
      if (i) res ~= ", ";
      res ~= Format(arg.type);
      if (arg.name) res ~= " "~arg.name;
      if (arg.initEx)
        res ~= Format(" = ", arg.initEx);
    }
    res ~= ")";
    return res;
  }
  override { // ScopeLike
    Statement[] getGuards() { return null; }
    int[] getGuardOffsets() { return null; }
    int framesize() {
      /* mixed frame on arm */
      if (isARM) return 4;
      else return 0;
    }
  }
  string fqn() {
    return get!(IModule).getIdentifier()~"."~name;
  }
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
      return cleaned_name~"_"~sup.mangle(null, type);
  }
  string exit() { return mangleSelf() ~ "_exit_label"; }
  static int funid_count;
  void addStatement(Statement st) {
    if (!tree) {
      if (auto sc = fastcast!(Scope) (st)) { tree = sc; return; }
      else tree = new Scope;
    }
    if (!fastcast!(Scope) (tree)) {
      logln(this);
      fail;
    }
    fastcast!(Scope) (tree).addStatement(st);
  }
  void dwarfOpen(AsmFile af) {
    auto dwarf2 = af.dwarf2;
    if (dwarf2) {
      auto sect = new Dwarf2Section(
        dwarf2.cache.getKeyFor("subprogram"));
      with (sect) {
        data ~= ".byte\t0x1"; // external
        data ~= dwarf2.strings.addString(pretty_name().replace("\"", "\\\""));
        data ~= qformat(".int\t",
          hex(af.getFileId(
            current_module().filename())));
        data ~= ".int\t0x0 /* line: todo */";
        data ~= ".byte\t0x1 /* prototyped */";
        sect.data ~= qformat(".long\t.LFB", funid_count);
        data ~= qformat(".long\t.LFE", funid_count);
        data ~= qformat(".byte\t1\t/* location description is one entry long */");
        data ~= qformat(".byte\t", hex(DW.OP_reg5), "\t/* ebp */");
      }
      dwarf2.open(sect);
    }
    if (dwarf2) {
      // for arguments
      auto sect = new Dwarf2Section(dwarf2.cache.getKeyFor("lexical block"));
      sect.data ~= qformat(".long\t.LFB", funid_count);
      sect.data ~= qformat(".long\t.LFE", funid_count);
      dwarf2.open(sect);
    }
    if (dwarf2) {
      foreach (param; type.params) if (param.name) if (auto var = fastcast!(Variable) (lookup(param.name, true))) {
        var.registerDwarf2(dwarf2);
      }
    }
  }
  void dwarfClose(AsmFile af) {
    if (af.dwarf2) {
      af.dwarf2.close;
      af.dwarf2.close;
    }
  }
  override {
    int framestart() { return _framestart; }
    bool addsSelf() { return true; }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      parseMe();
      inEmitAsm = true;
      scope(exit) inEmitAsm = false;
      
      if (af.floatStackDepth) {
        logln("garbage float stack when start-emitting ", this);
        fail;
      }
      
      auto fmn = mangleSelf(); // full mangled name
      af.put(".p2align 4");
      if (isWindoze()) {
        // af.put(".global ", fmn);
        if (weak) {
          if (fmn in symbol_emit_win32_hack_check) return; // fucking windows
          symbol_emit_win32_hack_check[fmn] = true;
          af.put(".global ", fmn);
        } else af.put(".global ", fmn);
      } else {
        af.put(".global ", fmn);
        if (weak) af.put(".weak ", fmn);
      }
      if (isWindoze()) {
        af.put(".def ", fmn, "; .val ", fmn, "; .scl 2; .type 32; .endef");
      } else {
        if (isARM)
          af.put(".type ", fmn, ", %function");
        else
          af.put(".type ", fmn, ", @function");
      }

      dwarfOpen(af);
      scope(exit) dwarfClose(af);

      af.put(fmn, ":"); // not really a label
      auto idnum = funid_count ++;
      af.put(".LFB", idnum, ":");
      af.jump_barrier();
      // af.put(".cfi_startproc");
      
      int psize;
      if (isARM) {
        // reconstruct a linear stackframe
        if (lookup("__base_ptr")) psize += 4;
        foreach (param; type.params) {
          psize += param.type.size;
        }
        if (psize <= 16 && psize%4 != 0) {
          logln("bad size ", type.params);
          // fail;
        }
        if (psize >= 16) af.pushStack("r3", 4);
        if (psize >= 12) af.pushStack("r2", 4);
        if (psize >= 8)  af.pushStack("r1", 4);
        if (psize >= 4)  af.pushStack("r0", 4);
        af.pushStack("fp, lr", 8);
        af.put("add fp, sp, #4");
      } else {
        af.pushStack("%ebp", nativePtrSize);
        af.mmove4("%esp", "%ebp");
        if (af.profileMode)
          af.put("call mcount");
      }
      
      auto backup = af.currentStackDepth;
      scope(exit) af.currentStackDepth = backup;
      af.currentStackDepth = framesize();
      if (!tree) { logln("Tree for ", this, " not generated! :( "); fail; }
      
      auto backupns = namespace();
      scope(exit) namespace.set(backupns);
      namespace.set(this);
      
      tree.emitAsm(af);
      
      if (type.ret != Single!(Void)) {
        funcall_emit_fun_end_guard (af, name);
      }
      
      af.emitLabel(exit(), keepRegs, isForward);
      
      // af.mmove4("%ebp", "%esp");
      // af.popStack("%ebp", nativePtrSize);
      if (isARM) {
        af.put("sub sp, fp, #4");
        af.popStack("fp, lr", 8);
        if (psize >= 16) af.sfree(16);
        else if (psize >= 12) af.sfree(12);
        else if (psize >= 8) af.sfree(8);
        else if (psize >= 4) af.sfree(4);
      } else {
        af.put("leave");
      }
      
      af.jump_barrier();
      if (isARM) {
        af.put("bx lr");
        af.pool;
      } else {
        af.put("ret");
      }
      if (isARM) {
        af.put(".ltorg");
      }
      af.put(".LFE", idnum, ":");
      if (!isWindoze())
        af.put(".size ", fmn, ", .-", fmn);
      if (af.floatStackDepth) {
        logln("leftover float stack when end-emitting ", this);
        fail;
      }
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
    if (auto res = super.lookup(name, local)) return res;
    return lookupInImports(name, local);
  }
  override Extensible extend(Extensible e2) {
    auto fun2 = fastcast!(Function) (e2);
    if (!fun2) {
      auto os2 = fastcast!(OverloadSet) (e2);
      if (!os2) {
        throw new Exception(Format("Can't overload function "
          "with non-function/overload set: ", this, " with ", e2, "!"
        ));
      }
      return new OverloadSet(name, this ~ os2.funs);
    }
    return new OverloadSet(name, this, fun2);
  }
  override Extensible simplify() { return this; }
}

class OverloadSet : Named, Extensible {
  string name;
  Function[] funs;
  this(string n, Function[] f...) {
    name = n;
    foreach (fun; f) add(fun);
  }
  override string toString() { return Format("overload of ", funs); }
  void add(Function f) {
    // don't add a function twice
    foreach (fun; funs) if (f is fun) return;
    if (f.extern_c) foreach (fun; funs) {
      if (fun.extern_c && fun.name == f.name) return;
    }
    funs ~= f;
  }
  override Extensible simplify() {
    if (funs.length == 1) return funs[0];
    return null;
  }
  protected this() { }
  override string getIdentifier() { return name; }
  override Extensible extend(Extensible e2) {
    auto fun2 = fastcast!(Function) (e2);
    if (!fun2) {
      auto os2 = fastcast!(OverloadSet) (e2);
      if (!os2) {
        throw new Exception(Format("Can't overload '", name,
          "' with non-function/overload set ", e2, "!"
        ));
      }
      auto res = new OverloadSet(name);
      res.funs = funs ~ os2.funs;
      return res;
    }
    auto res = new OverloadSet(name);
    res.funs = funs.dup;
    res.add(fun2);
    return res;
  }
}

class FunCall : Expr {
  Expr[] params;
  Function fun;
  Statement setup;
  Expr[] getParams() { return params; }
  FunCall construct() { return new FunCall; }
  FunCall dup() {
    auto res = construct;
    res.fun = fun.flatdup();
    if (setup) res.setup = setup.dup;
    
    foreach (param; params) res.params ~= param.dup;
    return res;
  }
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    fun.iterate(dg, IterMode.Semantic);
    defaultIterate!(params, setup).iterate(dg);
  }
  void emitWithArgs(AsmFile af, Expr[] args) {
    if (setup) setup.emitAsm(af);
    auto size = (Single!(Void) == fun.type.ret)?0:fun.type.ret.size;
    mixin(mustOffset("size"));
    callFunction(af, fun.type.ret, fun.extern_c, fun.type.stdcall, args, fun.getPointer());
  }
  override void emitAsm(AsmFile af) {
    emitWithArgs(af, params);
  }
  override string toString() { return Format("(", fun.name, "(", params, "))"); }
  override IType valueType() {
    if (!fun.type.ret) {
      if (fun.coarseSrc) {
        fun.parseMe;
        if (!fun.type.ret) {
          logln("wat");
          fail;
        }
      } else {
        logln("Function type not yet resolved but funcall type demanded: ", fun, " called with ", params);
        fail;
      }
    }
    return fun.type.ret;
  }
}

void handleReturn(IType ret, AsmFile af) {
  if (Single!(Void) == ret) return;
  if (isARM) {
    if (ret.size == 2) {
      af.salloc(2);
      af.mmove2("r0", "[sp]");
      return;
    }
    if (ret.size == 4) {
      af.pushStack("r0", 4);
      return;
    }
    if (ret.size == 8) {
      af.pushStack("r3", 4);
      af.pushStack("r0", 4);
      return;
    }
    if (ret.size == 12) {
      af.pushStack("r3", 4);
      af.pushStack("r2", 4);
      af.pushStack("r0", 4);
      return;
    }
    if (ret.size == 16) {
      af.pushStack("r3", 4);
      af.pushStack("r2", 4);
      af.pushStack("r1", 4);
      af.pushStack("r0", 4);
      return;
    }
    logln(ret);
    fail;
  }
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

import tools.log, ast.fold;
void callFunction(AsmFile af, IType ret, bool external, bool stdcall, Expr[] params, Expr fp) {
  if (!ret) throw new Exception("Tried to call function but return type not yet known! ");
  {
    // logln("CALL ", fp, " ", params);
    mixin(mustOffset("0", "outer"));
    string name;
    fp = foldex(fp);
    if (auto s = fastcast!(Symbol) (fp)) name = s.getName();
    else name = "(nil)";
    
    ret = resolveType(ret);
    if (!(ret.size == 1 /or/ 2 /or/ 4 /or/ 8 /or/ 12 /or/ 16 || cast(Void) ret))
      throw new Exception(Format("Return bug: ", ret, " from ", name, ": ",
      ret.size, " is ", (fastcast!(Object)~ ret).classinfo.name));
    af.comment("Begin call to ", name);
    
    bool backupESI = external && name != "setjmp";
    backupESI &= !isARM();
    
    if (backupESI) af.pushStack("%esi", nativePtrSize);
    if (isARM) { af.pushStack("r5", 4); } // used for call
    
    int paramsize;
    foreach (param; params) {
      auto sz = param.valueType().size;
      if (sz && sz < 4) sz = 4; // cdecl
      paramsize += sz;
    }
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
        // round to 4: cdecl treats <4b arguments as 4b (because push is 4b, presumably).
        auto sz = param.valueType().size;
        if (sz < 4) af.salloc(4 - sz);
        alignment_emitAligned(param, af);
      }
      
      if (fp.valueType().size > nativePtrSize) { logln("bad function pointer: ", fp); fail; }
      
      int inRegisters;
      if (isARM) {
        int effectivesize;
        foreach (param; params) effectivesize += param.valueType().size;
        void doPop(string reg) {
          // TODO: account for things like char
          if (effectivesize >= 4) {
            af.popStack(reg, 4);
            inRegisters += 4;
            effectivesize -= 4;
          }
        }
        fp.emitAsm(af);
        af.popStack("r5", 4); // must not be r0-r3 or r4!
        doPop("r0");
        doPop("r1");
        doPop("r2");
        doPop("r3");
      }
      
      if (isARM) {
        af.call("r5");
      } else {
        {
          mixin(mustOffset("nativePtrSize", "innerest"));
          fp.emitAsm(af);
        }
        af.popStack("%eax", 4);
        af.call("%eax");
      }
      
      foreach (param; params) {
        if (param.valueType() != Single!(Void)) {
          if (stdcall) {
            af.currentStackDepth -= param.valueType().size;
          } else {
            auto sz = param.valueType().size;
            if (sz < 4) sz = 4;
            af.sfree(sz);
          }
        }
      }
      af.salloc(inRegisters); // hax
    }
    
    bool returnsFPU = Single!(Float) == ret || Single!(Double) == ret;
    if (returnsFPU)
      af.floatStackDepth ++;
    
    while (restore--) {
      af.stackToFpu();
      if (returnsFPU)
        af.fpuOp("fxch");
    }
    af.sfree(alignCall);
    
    if (backupESI) af.popStack("%esi", nativePtrSize);
    if (isARM) af.popStack("r5", 4);
  }
  
  auto size = (Single!(Void) == ret)?0:ret.size;
  mixin(mustOffset("size"));
  handleReturn(ret, af);
}

class FunctionType : ast.types.Type {
  IType ret;
  Argument[] params;
  bool stdcall;
  override int size() {
    fail;
    assert(false);
  }
  IType[] types() {
    auto res = new IType[params.length];
    foreach (i, entry; params) res[i] = entry.type;
    return res;
  }
  override {
    int opEquals(IType it) {
      auto fun2 = fastcast!(FunctionType) (resolveType(it));
      if (!fun2) return false;
      if (ret != fun2.ret) return false;
      if (params.length != fun2.params.length) return false;
      foreach (i, param; params)
        if (param.type != fun2.params[i].type) return false;
      if (stdcall != fun2.stdcall) return false;
      return true;
    }
    bool isComplete() {
      if (!ret || !ret.isComplete) return false;
      foreach (par; params) if (!par.type.isComplete) return false;
      return true;
    }
    string mangle() {
      if (!ret) throw new Exception("Function return type indeterminate! ");
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

import ast.stringparse;
// generalized to reuse for nested funs
Object gotGenericFun(T, bool Decl, bool Naked = false)(T _fun, Namespace sup_override, bool addToNamespace,
                           ref string text, ParseCb cont, ParseCb rest, string forcename = null, bool shortform = false) {
  IType ptype;
  auto t2 = text;
  bool reassign;
  if (t2.accept("reassign")) reassign = true;
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
        shortform
        ||
        (test(ret = fastcast!(IType) (rest(t3, "type"))) && (t2 = t3, true))
        ||
        t2.accept("auto")
      )
      &&
      (
        forcename || t2.gotIdentifier(fun_name)
      )
      &&
      t2.gotParlist(_params, rest) || shortform
    )
  {
    if (ret) {
      auto sz = ret.size();
      if (sz > 16) t3.failparse("Return type must not be >16 bytes");
    }
    static if (is(typeof(_fun()))) auto fun = _fun();
    else auto fun = _fun;
    New(fun.type);
    fun.type.ret = ret;
    fun.type.params = _params;
    fun.name = forcename?forcename:fun_name;
    fun.reassign = reassign;
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
    
    if (addToNamespace) { fun.sup = null; ns.add(fun); if (!fun.sup) { logln("FAIL under ", ns, "! "); fail; } }
    text = t2;
    static if (Decl) {
      if (Naked || text.accept(";")) return fun;
      else t2.failparse("Expected ';'");
    } else {
      auto t4 = text;
      // if ret is null(auto), cannot wait to parse scope until later since we need the full type NOW
      if (fun.type.isComplete && t4.accept("{")) {
        auto block = text.coarseLexScope();
        fun.coarseSrc = block;
        fun.coarseContext = namespace();
        fun.coarseModule = current_module();
      }
      if (fun.coarseSrc) return fun;
      else {
        t2 = text;
        if (t2.accept(";")) { // undefined function
          fun.isabstract = true;
          text = t2;
          if (auto that = namespace().lookup("this"))
            fun.addStatement(
              iparse!(Statement, "undefined_function", "tree.stmt")
                    (`raise new Error "Function $this::$fun is not implemented";`, "fun", mkString(fun.name), "this", that));
          else
            fun.addStatement(
              iparse!(Statement, "undefined_function", "tree.stmt")
                    (`raise new Error "Function $fun is not implemented";`, "fun", mkString(fun.toString())));
          return fun;
        }
        Scope sc;
        if (rest(text, "tree.scope", &sc)) {
          if (!fun.type.ret)
            fun.type.ret = Single!(Void); // implicit return
          fun.addStatement(sc);
          return fun;
        } else text.failparse("Couldn't parse function scope");
      }
    }
  } else return null;
}

Object gotGenericFunDef(T)(T fun, Namespace sup_override, bool addToNamespace, ref string text, ParseCb cont, ParseCb rest, string forcename = null, bool shortform = false) {
  return gotGenericFun!(T, false)(fun, sup_override, addToNamespace, text, cont, rest, forcename, shortform);
}
Object gotGenericFunDecl(T)(T fun, Namespace sup_override, bool addToNamespace, ref string text, ParseCb cont, ParseCb rest, string forcename = null, bool shortform = false) {
  return gotGenericFun!(T, true)(fun, sup_override, addToNamespace, text, cont, rest, forcename, shortform);
}
// without semicolon required
Object gotGenericFunDeclNaked(T)(T fun, Namespace sup_override, bool addToNamespace, ref string text, ParseCb cont, ParseCb rest, string forcename = null, bool shortform = false) {
  return gotGenericFun!(T, true, true)(fun, sup_override, addToNamespace, text, cont, rest, forcename, shortform);
}

Object gotFunDef(bool ExternC)(ref string text, ParseCb cont, ParseCb rest) {
  auto fun = new Function;
  fun.extern_c = ExternC;
  return gotGenericFunDef(fun, cast(Namespace) null, true, text, cont, rest);
}
mixin DefaultParser!(gotFunDef!(false), "tree.fundef");
mixin DefaultParser!(gotFunDef!(true), "tree.fundef_externc");

// ensuing code gleefully copypasted from nestfun
// yes I wrote delegates first. how about that.
class FunctionPointer : ast.types.Type {
  IType ret;
  Argument[] args;
  bool stdcall;
  this() { }
  string toString() { return Format(ret, " function(", args, ")", stdcall?" stdcall":""); }
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
  int opEquals(IType type2) {
    auto t2 = resolveType(type2);
    auto ft = fastcast!(FunctionPointer) (t2);
    if (!ft) return false;
    if (ret != ft.ret) return false;
    if (args.length != ft.args.length) return false;
    foreach (i, p; args) if (p.type != ft.args[i].type) return false;
    if (stdcall != ft.stdcall) return false;
    return true;
  }
  override string mangle() {
    auto res = "fp_ret_"~ret.mangle()~"_args";
    if (!args.length) res ~= "_none";
    else foreach (arg; args)
      res ~= "_"~arg.type.mangle();
    return res;
  }
  override bool isComplete() {
    if (!ret || !ret.isComplete) return false;
    foreach (arg; args) if (!arg.type.isComplete) return false;
    return true;
  }
}

// &fun
class FunRefExpr : Expr, Literal {
  Function fun;
  this(Function fun) { this.fun = fun; }
  private this() { }
  mixin DefaultDup!();
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    fun.iterate(dg, IterMode.Semantic);
  }
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
