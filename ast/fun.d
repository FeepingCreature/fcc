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
  string toString() { if (initEx) return qformat(type, " "[], name, " = ", initEx); return qformat(type, " "[], name); }
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
      foreach (entry; fun.type.params) {
        auto sz = entry.type.size();
        if (sz < 4) sz = 4;
        size += sz;
      }
      res ~= qformat("@"[], size);
    }
    return res;
  }
  this(Function fun) {
    this.fun = fun;
    super();
  }
  private this() { }
  mixin DefaultDup!();
  string toString() { return qformat("symbol<"[], fun, ">"[]); }
  IType vt_cache;
  override IType valueType() {
    if (!vt_cache) {
      auto fp = new FunctionPointer;
      fp.ret = fun.type.ret;
      fp.args = fun.type.params;
      fp.args ~= Argument(Single!(SysInt));
      fp.stdcall = fun.type.stdcall;
      vt_cache = fp;
    }
    return vt_cache;
  }
}

extern(C) Object nf_fixup__(Object obj, Expr mybase);

extern(C) void funcall_emit_fun_end_guard(AsmFile af, string name);

TLS!(Function) current_emitting_function;
static this() { New(current_emitting_function); }

class Function : Namespace, Tree, Named, SelfAdding, IsMangled, FrameRoot, Extensible, ScopeLike, EmittingContext, Importer {
  string name;
  Expr getPointer() {
    return fastalloc!(FunSymbol)(this);
  }
  int idnum;
  static int funid_count;
  this() { idnum = funid_count ++; }
  FunctionType type;
  Tree tree;
  bool extern_c = false, weak = false, reassign = false, isabstract = false, optimize = false;
  void markWeak() { weak = true; }
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    if (mode == IterMode.Lexical) { parseMe; defaultIterate!(tree).iterate(dg, mode); }
    // else to be defined in subclasses
  }
  string toString() { return qformat("fun "[], name, " "[], type, " <- "[], sup); }
  // add parameters to namespace
  int _framestart;
  string coarseSrc;
  IModule coarseModule;
  bool inEmitAsm, inParse, inFixup /* suppress fixup -> add -> lookup -> parseMe chain */;
  override bool isBeingEmat() { return inEmitAsm; }
  void parseMe() {
    if (!coarseSrc) return;
    if (inFixup) return;
    if (type.args_open) {
      logln("Tried to parse function but function has open args: ", this);
      fail;
    }
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    if (tree) namespace.set(fastcast!(Scope) (tree));
    else namespace.set(this);
    
    /**
     * No! Bad! Wrong!
     * current_module is for emitting, not for parsing;
     * and the module of a function might have already been emat by this point!
     * for instance if it's a template
     * ON THE OTHER HAND, sometimes this helps prevent linker errors.
     * Compromise: override iff the coarse module has not yet been emat
     **/
    auto backupmod = current_module();
    scope(exit) current_module.set(backupmod);
    if (!coarseModule.getDoneEmitting()) current_module.set(coarseModule);
    
    // logln("parse function ", name, " in ", coarseContext, ": ", coarseSrc.ptr);
    
    // needed because we may be a template function (!)
    auto popCache = pushCache(); scope(exit) popCache();
    
    string t2 = coarseSrc;
    coarseSrc = null;
    
    inParse = true;
    scope(exit) inParse = false;
    
    auto s = sup;
    auto stmt = fastcast!(Statement) (parse(t2, "tree.scope"));
    if (!stmt) {
      // fail();
      t2.failparse("Couldn't parse function scope");
    }
    addStatement(stmt);
    opt(tree);
    
    if (!type.ret)
      type.ret = Single!(Void); // implicit return
    
    t2 = t2.mystripl();
    if (t2.length)
      t2.failparse("Unknown text! ");
  }
  mixin ImporterImpl!(parseMe);
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
    inFixup = true; scope(exit) inFixup = false;
    // cdecl: 0 old ebp, 4 return address, 8 parameters
    int cur;
    if (isARM) {
      add(fastalloc!(Variable)(Single!(SizeT), "__old_ebp"[], -4));
      add(fastalloc!(Variable)(Single!(SizeT), "__fun_ret"[], 0));
      cur = _framestart = 4;
    } else {
      add(fastalloc!(Variable)(Single!(SizeT), "__old_ebp"[], 0));
      add(fastalloc!(Variable)(Single!(SizeT), "__fun_ret"[], 4));
      cur = _framestart = 8;
      if (isWindoze() && extern_c) {
        // ebx backup
        add(fastalloc!(Variable)(Single!(SizeT), "__ebx_backup"[], -4));
      }
    }
    if (type.ret && type.ret.returnsInMemory()) {
      auto pt = fastalloc!(Pointer)(type.ret);
      add(fastalloc!(Variable)(pt, "__return_pointer", cur));
      _framestart += pt.size;
      cur += pt.size;
    }
    // TODO: 16-byte? alignment
    foreach (param; type.params) {
      auto pt = param.type;
      if (!pt) {
        logln("Function parameter type still undefined in ", name, ": ", param.name);
        asm { int 3; }
        // throw new Exception(qformat("Function parameter type still undefined in ", name, ": ", param.name));
      }
      _framestart += pt.size;
      add(fastalloc!(Variable)(pt, param.name, cur));
      cur += pt.size;
      cur = (cur + 3) & ~3; // round to 4
    }
    if (!releaseMode) {
      if (tree) {
        logln(tree);
        fail;
      }
    }
    return cur;
  }
  string cleaned_name() { return name.cleanup(); }
  string pretty_name() {
    auto mod = get!(IModule).modname();
    auto res = qformat(type.ret, " "[], mod, "."[], name);
    res ~= "(";
    foreach (i, arg; type.params) {
      if (i) res ~= ", ";
      res ~= Format(arg.type);
      if (arg.name) res ~= " "~arg.name;
      if (arg.initEx)
        res ~= Format(" = "[], arg.initEx);
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
      else if (isWindoze() && extern_c) return 4; // ebx backup
      else return 0;
    }
  }
  string fqn() {
    return get!(IModule).getIdentifier()~"."~name;
  }
  string cached_selfmangle;
  override string mangleSelf() {
    if (cached_selfmangle) return cached_selfmangle;
    if (extern_c) {
      auto res = cleaned_name;
      if (platform_prefix == "i686-mingw32-") {
        res = "_"~res;
        if (res == "_setjmp") res = "__setjmp"; // lol wat.
      }
      cached_selfmangle = res;
    } else if (name == "__c_main") {
      cached_selfmangle = "main";
      return "main";
    } else if (name == "__win_main") {
      if (platform_prefix == "i686-mingw32-") {
        cached_selfmangle = "_WinMain@16";
      } else {
        cached_selfmangle = "_WinMain_not_relevant_on_this_architecture";
      }
    } else
      cached_selfmangle = cleaned_name~"_"~sup.mangle(null, type);
    return cached_selfmangle;
  }
  string exit() { return mangleSelf() ~ "_exit_label"; }
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
      auto sect = fastalloc!(Dwarf2Section)(
        dwarf2.cache.getKeyFor("subprogram"));
      with (sect) {
        data ~= ".byte\t0x1"; // external
        data ~= dwarf2.strings.addString(pretty_name().replace("\"", "\\\""));
        data ~= qformat(".int\t"[],
          hex(af.getFileId(
            current_module().filename())));
        data ~= ".int\t0x0 /* line: todo */";
        data ~= ".byte\t0x1 /* prototyped */";
        sect.data ~= qformat(".long\t.LFB"[], idnum);
        data ~= qformat(".long\t.LFE"[], idnum);
        data ~= qformat(".byte\t1\t/* location description is one entry long */"[]);
        data ~= qformat(".byte\t"[], hex(DW.OP_reg5), "\t/* ebp */"[]);
      }
      dwarf2.open(sect);
    }
    if (dwarf2) {
      // for arguments
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("lexical block"[]));
      sect.data ~= qformat(".long\t.LFB"[], idnum);
      sect.data ~= qformat(".long\t.LFE"[], idnum);
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
  string fun_start_sym() { return qformat(".LFB"[], idnum); }
  string fun_end_sym() { return qformat(".LFE"[], idnum); }
  string fun_linenr_sym() { return qformat(".DebugInfo_LineInfo"[], idnum); }
  int[] linenumbers;
  int linecounter;
  string linedebug(int id) {
    return qformat(".DebugInfo_"[], idnum, "_Line_"[], id);
  }
  void add_line_number(AsmFile af, int line) {
    af.put(linedebug(linecounter++), ":"[]);
    linenumbers ~= line;
  }
  override {
    int framestart() { return _framestart; }
    bool addsSelf() { return true; }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      auto cef_backup = current_emitting_function();
      current_emitting_function.set(this);
      scope(exit) current_emitting_function.set(cef_backup);
      
      auto backup_opt = af.optimize, backup_rm = releaseMode, backup_dbg = af.debugMode;
      auto backup_dwarf = af.dwarf2;
      scope(exit) {
        af.optimize = backup_opt;
        releaseMode = backup_rm;
        af.debugMode = backup_dbg;
        af.dwarf2 = backup_dwarf;
      }
      
      parseMe();
      if (optimize) {
        af.flush();
        af.optimize = true;
        // still emit line number info when -g is on, even in pragma(fast)
        // af.debugMode = false;
        // ...... why?
        af.debugMode = false;
        af.dwarf2 = null;
      }
      
      inEmitAsm = true;
      scope(exit) inEmitAsm = false;
      
      if (af.floatStackDepth) {
        logln("garbage float stack when start-emitting ", this);
        fail;
      }
      
      auto fmn = mangleSelf(); // full mangled name
      af.put(".p2align 4"[]);
      if (isWindoze()) {
        af.put(".section .text$section_for_"[], fmn, ", \"ax\""[]);
        af.put(".linkonce discard"[]);
        af.put(".globl "[], fmn);
      } else {
        af.put(".global "[], fmn);
        if (weak) af.put(".weak "[], fmn);
      }
      if (isWindoze()) {
        af.put(".def "[], fmn, "; .val "[], fmn, "; .scl 2; .type 32; .endef"[]);
      } else {
        if (isARM)
          af.put(".type "[], fmn, ", %function"[]);
        else
          af.put(".type "[], fmn, ", @function"[]);
      }
      
      dwarfOpen(af);
      scope(exit) dwarfClose(af);
      
      af.put(fmn, ":"[]); // not really a label
      af.put(".global "[], fun_start_sym());
      af.put(fun_start_sym(), ":"[]);
      // af.put(".cfi_startproc"[]);
      
      af.jump_barrier();
      
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
        af.put("add fp, sp, #4"[]);
      } else {
        af.pushStack("%ebp", nativePtrSize);
        af.mmove4("%esp", "%ebp");
        if (isWindoze() && extern_c) { af.pushStack("%ebx", nativePtrSize); }
        if (af.profileMode)
          af.put("call mcount"[]);
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
        af.put("sub sp, fp, #4"[]);
        af.popStack("fp, lr", 8);
        if (psize >= 16) af.sfree(16);
        else if (psize >= 12) af.sfree(12);
        else if (psize >= 8) af.sfree(8);
        else if (psize >= 4) af.sfree(4);
      } else {
        if (isWindoze() && extern_c) { af.mmove4("-4(%ebp)", "%ebx"); }
        af.put("leave"[]);
      }
      
      af.jump_barrier();
      if (isARM) {
        af.put("bx lr"[]);
        af.pool;
      } else {
        if (type.ret.returnsInMemory()) {
          af.put("ret $4"); // clean off pointer
        } else {
          af.put("ret");
        }
      }
      if (isARM) {
        af.put(".ltorg"[]);
      }
      
      af.put(".global "[], fun_end_sym());
      af.put(fun_end_sym(), ":"[]);
      
      if (!isWindoze())
        af.put(".size "[], fmn, ", .-"[], fmn);
      
      if (isWindoze()) af.put(".section .text$debug_section_"[], fmn, ", \"r\""[]);
      af.put(".global "[], fun_linenr_sym());
      af.put(fun_linenr_sym(), ":"[]);
      af.put(".long "[], linecounter);
      for (int i = 0; i < linecounter; ++i) {
        af.put(".long "[], linedebug(i));
        af.put(".long "[], linenumbers[i]);
      }
      
      if (isWindoze()) {
        af.put(".section rodata");
      }
      
      if (af.floatStackDepth) {
        logln("leftover float stack when end-emitting ", this);
        fail;
      }
      if (optimize) {
        af.flush;
      }
      // af.put(".cfi_endproc"[]);
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
    parseMe;
    if (auto res = super.lookup(name, true)) return res;
    if (auto res = lookupInImports(name, local)) return res;
    if (local) return null;
    return super.lookup(name, local);
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
      return fastalloc!(OverloadSet)(name, this ~ os2.funs);
    }
    return fastalloc!(OverloadSet)(name, this, fun2);
  }
  override Extensible simplify() { return this; }
}

void mkAbstract(Function fun) {
  fun.isabstract = true;
  if (auto that = namespace().lookup("this"[]))
    fun.addStatement(
      iparse!(Statement, "undefined_function"[], "tree.stmt"[])
            (`raise new Error "Function $this::$fun is not implemented";`, "fun"[], mkString(fun.name), "this"[], that));
  else
    fun.addStatement(
      iparse!(Statement, "undefined_function"[], "tree.stmt"[])
            (`raise new Error "Function $fun is not implemented";`, "fun"[], mkString(fun.toString())));
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
      auto res = fastalloc!(OverloadSet)(name);
      res.funs = funs ~ os2.funs;
      return res;
    }
    auto res = fastalloc!(OverloadSet)(name);
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
  if (ret.returnsInMemory()) {
    // the funcall routine already allocated space for us in just
    // the right spot, so we actually have nothing left to do.
    return;
  }
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
  auto size = (Single!(Void) == ret)?0:ret.size;
  mixin(mustOffset("size"));
  {
    // logln("CALL ", fp, " ", params, " => ", ret);
    string name;
    opt(fp);
    if (auto s = fastcast!(Symbol) (fp)) name = s.getName();
    else name = "(nil)";
    
    ret = resolveType(ret);
    if (!(ret.size == 1 /or/ 2 /or/ 4 /or/ 8 /or/ 12 /or/ 16 || cast(Void) ret))
      throw new Exception(Format("Return bug: ", ret, " from ", name, ": ",
      ret.size, " is ", (fastcast!(Object)~ ret).classinfo.name));
    debug af.comment("Begin call to "[], name);
    
    bool returnInMemory = ret.returnsInMemory();
    string ret_location;
    if (returnInMemory) {
      af.salloc(ret.size);
      ret_location = qformat(-af.currentStackDepth, "(%ebp)");
    }
    
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
    
    // distance to alignment border
    auto align_offset = af.currentStackDepth + esp_alignment_delta;
    if (returnInMemory) align_offset += 4;
    // what do we have to do to align the callsite?
    auto alignCall = 16 - (align_offset + paramsize) % 16;
    if (alignCall == 16) alignCall = 0;
    // logln("at call to ", name, ", depth is ", af.currentStackDepth, " and ", align_offset, " and ", alignCall, " due to ", paramsize);
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
        if (sz && sz < 4) af.salloc(4 - sz);
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
        // af.put("test $15, %esp; jz 1f; call abort; 1:");
        if (ret_location) {
          af.loadAddress(ret_location, "%ebx");
          af.pushStack("%ebx", 4);
        }
        if (af.currentStackDepth % 16 != 8) {
          logln("at call, depth is ", af.currentStackDepth, " ", af.currentStackDepth % 16);
          logln("thus, unaligned! :o");
          fail;
        }
        af.call("%eax");
        if (ret_location) {
          // eaten by callee
          af.currentStackDepth -= 4;
        }
      }
      
      foreach (param; params) {
        if (param.valueType() != Single!(Void)) {
          auto sz = param.valueType().size;
          if (sz && sz < 4) sz = 4;
          if (stdcall) {
            af.currentStackDepth -= sz;
          } else {
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
  
  handleReturn(ret, af);
}

class FunctionType : ast.types.Type {
  IType ret;
  Argument[] params;
  bool stdcall;
  FunctionType dup() {
    auto res = fastalloc!(FunctionType)();
    res.ret = ret;
    res.params = params.dup;
    res.stdcall = stdcall;
    return res;
  }
  bool args_open() {
    foreach (arg; params) if (!arg.type) return true;
    return false;
  }
  bool types_open() {
    if (!ret) return true;
    return args_open();
  }
  override int size() {
    fail;
    assert(false);
  }
  IType[] types() {
    auto res = new IType[params.length];
    foreach (i, entry; params) res[i] = entry.type;
    return res;
  }
  IType[] alltypes() {
    auto res = new IType[params.length + 1];
    res[0] = ret;
    foreach (i, entry; params) res[i+1] = entry.type;
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
      // if (!ret) { logln("Function return type indeterminate! "); fail; }
      string[] res;
      // res ~= "function_to_";
      // res ~= ret.mangle();
      res ~= "function";
      if (params.length) foreach (i, param; params) {
        if (!i) res ~= "_of_";
        else res ~= "_and_";
        res ~= param.type.mangle();
      }
      return res.qjoin();
    }
    string toString() { return Format("Function of "[], params, " => "[], ret); }
  }
}

bool gotParlist(ref string str, ref Argument[] res, ParseCb rest, bool allowNull) {
  auto t2 = str;
  IType ptype, lastType;
  string parname;
  Expr init;
  bool gotInitializer(ref string text, out Expr res) {
    auto t2 = text;
    if (!t2.accept("=")) return false;
    if (!rest(t2, "tree.expr"[], &res))
      return false;
    text = t2;
    return true;
  }
  if (!t2.accept("(")) return false;
  
  if (t2.bjoin(
        ( // can omit types for subsequent parameters
          test(ptype = fastcast!(IType)~ rest(t2, "type")) || test(ptype = lastType) || allowNull
        ) && (
          t2.gotIdentifier(parname) || ((parname = null), true)
        ) && (
          gotInitializer(t2, init) || ((init = null), true)
        ),
        t2.accept(","[]),
        { lastType = ptype; if (ptype || parname) res ~= Argument(ptype, parname, init); }
      ) &&
      t2.accept(")"[])
  ) {
    str = t2;
    return true;
  } else {
    t2.failparse("Failed to get parameter list"[]);
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
  if (t2.accept("reassign"[])) reassign = true;
  string parname;
  *error.ptr() = stuple(""[], ""[]);
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
        (test(ret = fastcast!(IType) (rest(t3, "type"[]))) && (t2 = t3, true))
        ||
        t2.accept("auto"[])
      )
      &&
      (
        forcename || t2.gotIdentifier(fun_name)
      )
      &&
      t2.gotParlist(_params, rest, true) || shortform
    )
  {
    if (ret) {
      auto sz = ret.size();
      if (sz > 16) t3.failparse("Return type must not be >16 bytes"[]);
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
    
    if (fun.name == "main"[]) {
      if (gotMain) {
        t2.failparse("Main already defined! "[]);
      }
      gotMain = fun;
      fun.name = "__fcc_main";
    }
    
    if (!fun.type.args_open) fun.fixup;
    
    if (addToNamespace) { fun.sup = null; ns.add(fun); if (!fun.sup) { logln("FAIL under "[], ns, "! "[]); fail; } }
    text = t2;
    static if (Decl) {
      if (Naked || text.accept(";"[])) return fun;
      else t2.failparse("Expected ';'"[]);
    } else {
      auto t4 = text;
      // if ret is null(auto), cannot wait to parse scope until later since we need the full type NOW
      // do we really, though? We can grab it when we need it ..
      /*
        compromise: if ret is null, and we are NOT also doing parameter deduction, parse it immediately
        // == if ret or we have open params, delay parsing
        parameter deduction is the only reason to delay.
      */
      if ((fun.type.isComplete || fun.type.args_open) && t4.canCoarseLexScope()) {
        auto block = text.coarseLexScope();
        fun.coarseSrc = block;
        auto cur_ns = namespace();
        if (cur_ns !is fun) { logln("huh. ", cur_ns, " ||| ", fun); fail; }
        fun.coarseModule = current_module();
      }
      if (fun.coarseSrc) return fun;
      else {
        if (fun.type.args_open) {
          t2.failparse("Could not delay function parsing but type not yet known");
        }
        t2 = text;
        if (t2.accept(";"[])) { // undefined function
          text = t2;
          mkAbstract(fun);
          return fun;
        }
        Scope sc;
        if (rest(text, "tree.scope"[], &sc)) {
          if (!fun.type.ret)
            fun.type.ret = Single!(Void); // implicit return
          fun.addStatement(sc);
          return fun;
        } else text.failparse("Couldn't parse function scope"[]);
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
mixin DefaultParser!(gotFunDef!(false), "tree.fundef"[]);
mixin DefaultParser!(gotFunDef!(true), "tree.fundef_externc"[]);

// ensuing code gleefully copypasted from nestfun
// yes I wrote delegates first. how about that.
class FunctionPointer : ast.types.Type {
  IType ret;
  Argument[] args;
  bool stdcall;
  this() { }
  string toString() { return Format(ret, " function("[], args, ")"[], stdcall?" stdcall":""[]); }
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
  string manglecache;
  override string mangle() {
    if (manglecache) return manglecache;
    auto res = "fp_ret_"~ret.mangle()~"_args";
    if (!args.length) res ~= "_none";
    else foreach (arg; args)
      res ~= "_"~arg.type.mangle();
    manglecache = res;
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
  IType typecache;
  override {
    IType valueType() {
      if (!typecache) typecache = fastalloc!(FunctionPointer)(fun);
      return typecache;
    }
    void emitAsm(AsmFile af) {
      auto c = new Constant(fun.mangleSelf());
      c.emitAsm(af);
      delete c;
    }
    string getValue() { return fun.mangleSelf(); }
  }
}

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb rest) {
    IType ptype;
    Argument[] list;
    auto t2 = text;
    if (t2.accept("function"[]) &&
      t2.gotParlist(list, rest, false)
    ) {
      text = t2;
      auto res = new FunctionPointer;
      res.ret = cur;
      res.args = list.dup;
      return res;
    } else return null;
  };
}
