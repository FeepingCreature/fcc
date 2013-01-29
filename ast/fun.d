module ast.fun;

import ast.namespace, ast.base, ast.variable, llvmfile, ast.types, ast.scopes,
  ast.pointer, ast.literals, ast.vardecl, ast.assign, ast.casting;

private alias parseBase.startsWith startsWith;
private alias parseBase.endsWith endsWith;

import tools.functional;
import dwarf2;

// workaround for inability to import ast.modules
interface StoresDebugState {
  bool hasDebug();
}

extern(C) void alignment_emitAligned(Expr ex, LLVMFile lf);

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

string declare(Function fun, string name) {
  string argstr;
  foreach (par; fun.getParams(true)) {
    if (argstr) argstr ~= ", ";
    argstr ~= typeToLLVM(par.type, true);
  }
  string callconv;
  if (fun.type.stdcall) callconv = "x86_stdcallcc ";
  string flags;
  if (name == "setjmp") flags = " returns_twice";
  return qformat("declare ", callconv, typeToLLVM(fun.type.ret), " @", name, "(", argstr, ")", flags);
}

class FunSymbol : Symbol {
  Function fun;
  IType nested;
  string getName() {
    string res = fun.mangleSelf();
    if (fun.type.stdcall) {
      // todo("find a way to compute (guess?) stdcall size");
      /*int size;
      foreach (entry; fun.type.params) {
        auto sz = entry.type.size();
        if (sz < 4) sz = 4;
        size += sz;
      }
      res ~= qformat("@"[], size);*/
    }
    return res;
  }
  this(Function fun, IType nested = null) {
    this.fun = fun;
    this.nested = nested;
    if (fastcast!(Object)(fun).classinfo.name.find("nestfun") != -1 && !nested)
      fail;
    super(null, fun.type);
  }
  override FunSymbol dup() {
    return new FunSymbol(fun, nested);
  }
  override void emitLLVM(LLVMFile lf) {
    if (once(lf, "symbol ", getName())) {
      lf.decls[getName()] = declare(fun, getName());
    }
    push(lf, "@", getName());
  }
  string toString() { return qformat("funsymbol<"[], fun, ">"[]); }
  IType vt_cache;
  IType _valueType() {
    auto fp = new FunctionPointer(fun);
    if (nested) fp.args ~= Argument(nested);
    fp.stdcall = fun.type.stdcall;
    return fp;
  }
  override mixin memoize!(_valueType, vt_cache, "valueType");
}

extern(C) Object nf_fixup__(Object obj, Expr mybase);

extern(C) void funcall_emit_fun_end_guard(LLVMFile lf, string name);

pragma(set_attribute, recordFrame, externally_visible);
extern(C) void recordFrame(Scope sc) {
  auto fun = sc.get!(Function);
  if (!fun) {
    logln("no fun under ", sc);
    fail;
  }
  /*if (fun.mangleSelf() == "reverse_module_std_0E_util__of_function_of_rich_auto_array_of_tuple__ref_module_gui_0E_base_Widget_int__templinst_reverse_with_rich_auto_array_of_tuple__ref_module_gui_0E_base_Widget_int") {
    string stackinfo;
    foreach (entry; sc.stackframe()) {
      if (stackinfo) stackinfo ~= ", ";
      stackinfo ~= qformat(entry._0, ": ", entry._1);
    }
    logln("record for ", cast(void*) fun, " ", fun.name, /*" (", fun.getParams(true), "), * /": ", frametype2(sc), " from ", stackinfo, ": ", sc.field);
  }*/
  fun.llvmFrameTypes ~= frametype2(sc);
}

extern(C) {
  void addFailureFun(Function fun);
  Expr C_mkMemberAccess(Expr strct, string name);
  Expr C_mkDgConstructExpr(Expr r, Expr ptrval);
  Function C_mkPFNestFun(Expr dgex);
}
class Function : Namespace, Tree, Named, SelfAdding, IsMangled, Extensible, ScopeLike, EmittingContext, Importer {
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
  Function[] dependents; // functions that are only needed inside this function and thus should get emitted into the same module.
  override void markWeak() { weak = true; foreach (dep; dependents) dep.markWeak; }
  override void markExternC() { extern_c = true; }
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    if (mode == IterMode.Lexical) { parseMe; defaultIterate!(tree).iterate(dg, mode); }
    defaultIterate!(dependents).iterate(dg, mode);
    // else to be defined in subclasses
  }
  string toString() { return qformat("fun "[], name, " "[], type/*, " <- "[], sup*/); }
  string[] llvmFrameTypes;
  // add parameters to namespace
  string coarseSrc;
  IModule coarseModule;
  bool inEmitAsm, inParse, inFixup /* suppress fixup -> add -> lookup -> parseMe chain */;
  bool leaveFragmentText; // set coarseSrc to leftover text when done - for supporting void foo() statement_here; type funs
  bool alreadyEmat; // debugging
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
    
    // backup for pragma(fast);
    auto modebackup = releaseMode;
    scope(exit) releaseMode = modebackup;
    
    /**
     * No! Bad! Wrong!
     * current_module is for emitting, not for parsing;
     * and the module of a function might have already been emat by this point!
     * for instance if it's a template
     * ON THE OTHER HAND, sometimes this helps prevent linker errors.
     * Compromise: override iff the coarse module has not yet been emat
     * 11-8-12 NO COMPROMISE NO SURRENDER. (also this breaks incremental build)
     * If there are errors, fix them at the source.
     **/
    /*auto backupmod = current_module();
    scope(exit) current_module.set(backupmod);
    if (!coarseModule.getDoneEmitting()) current_module.set(coarseModule);*/
    
    // logln("parse function ", name, " in ", coarseContext, ": ", coarseSrc.ptr);
    
    // needed because we may be a template function (!)
    auto popCache = pushCache(); scope(exit) popCache();
    
    string t2 = coarseSrc;
    coarseSrc = null;
    
    inParse = true;
    scope(exit) inParse = false;
    
    // if (this.name == "assert")
      // logln("add? for ", this, " (", releaseMode, ") - ", lookup("__frameinfo", true), " - ", lookup(tlsbase, true));
    if (lookup("__frameinfo", true) && lookup(tlsbase, true) && sysmod.lookup("__popFrameInfo")) {
      if (!releaseMode) {
        auto infovar = fastcast!(LValue)(lookup("__frameinfo", true));
        auto sys_frameinfo = fastcast!(Expr)(sysmod.lookup("frameinfo"));
        
        // __frameinfo.fun = fqn()
        addStatement(mkAssignment(C_mkMemberAccess(infovar, "fun"), mkString(fqn())));
        // __frameinfo.pos = "initialpos"
        {
          auto pos = lookupPos(t2);
          auto line = pos._0, name = pos._2;
          addStatement(mkAssignment(C_mkMemberAccess(infovar, "pos"), mkString(qformat(name, ":", line))));
        }
        // __frameinfo.prev = frameinfo
        addStatement(mkAssignment(C_mkMemberAccess(infovar, "prev"), sys_frameinfo));
        // frameinfo = &__frameinfo
        addStatement(mkAssignment(sys_frameinfo, fastalloc!(RefExpr)(infovar)));
        
        auto popFrameInfo = fastcast!(Function)(sysmod.lookup("__popFrameInfo"));
        if (!popFrameInfo) fail;
        
        auto r = fastalloc!(FunRefExpr)(popFrameInfo);
        auto ptrval = reinterpret_cast(voidp, fastalloc!(RefExpr)(infovar));
        auto dgex = C_mkDgConstructExpr(r, ptrval);
        auto pfun = C_mkPFNestFun(dgex);
        
        auto sc = fastcast!(Scope)(tree);
        if (!sc) fail;
        namespace.set(sc);
        // onSuccess frameinfo = __frameinfo.prev
        sc.addGuard(mkAssignment(fastcast!(Expr)(sysmod.lookup("frameinfo")), C_mkMemberAccess(infovar, "prev")));
        // onFailure frameinfo = __frameinfo.prev
        addFailureFun(pfun);
      }
    }/* else if (lookup(tlsbase, true)) logln("don't add for ", this.name, " because no _threadlocal");
    else logln("don't add for ", this.name, " because no __frameinfo");*/
    
    if (tree) namespace.set(fastcast!(Scope)(tree));
    
    auto s = sup;
    auto stmt = fastcast!(Statement) (parse(t2, "tree.scope"));
    if (!stmt) {
      // fail();
      t2.failparse("Couldn't parse function scope");
    }
    if (tree) fastcast!(Scope)(tree).addStatement(stmt);
    else addStatement(stmt);
    opt(tree);
    
    if (!type.ret)
      type.ret = Single!(Void); // implicit return
    
    auto t3 = t2.mystripl();
    if (t3.length) {
      if (leaveFragmentText) coarseSrc = t2;
      else t3.failparse("Unknown text! ");
    }
  }
  mixin ImporterImpl!(parseMe);
  Argument[] getParams(bool implicits) {
    if (implicits) {
      if (!extern_c && (!type.params.length || Single!(Variadic) != type.params[$-1].type))
        return type.params ~ Argument(voidp, tlsbase);
    }
    return type.params;
  }
  Function flatdup() { // NEVER dup the tree!
    auto res = alloc();
    res.name = name;
    res.type = type;
    res.weak = weak;
    res.extern_c = extern_c;
    res.tree = tree;
    res.coarseSrc = coarseSrc;
    res.llvmFrameTypes = llvmFrameTypes;
    res.coarseModule = coarseModule;
    res.sup = sup;
    res.field = field;
    res.dependents = dependents.dup;
    res.rebuildCache;
    return res;
  }
  Function dup() {
    auto res = flatdup();
    if (tree) {
      auto backup = namespace();
      scope(exit) namespace.set(backup);
      namespace.set(res);
      res.tree = tree.dup;
    }
    foreach (ref dep; dependents) dep = dep.dup;
    res.coarseSrc = coarseSrc;
    return res;
  }
  FunCall mkCall() {
    auto res = new FunCall;
    res.fun = this;
    return res;
  }
  int fixup() {
    if (field.length) fail;
    int res;
    inFixup = true; scope(exit) inFixup = false;
    
    auto backup = namespace(); scope(exit) namespace.set(backup);
    namespace.set(this);
    
    foreach (param; getParams(true)) {
      auto pt = param.type;
      if (!pt) {
        logln("Function parameter type still undefined in ", name, ": ", param.name);
        asm { int 3; }
        // throw new Exception(qformat("Function parameter type still undefined in ", name, ": ", param.name));
      }
      add(fastalloc!(Variable)(pt, res++, param.name));
    }
    if (auto fi = fastcast!(IType)(sysmod.lookup("FrameInfo"))) {
      // logln("add frame info to ", name);
      add(fastalloc!(Variable)(fi, res++, "__frameinfo"));
    }
    if (!releaseMode) {
      if (tree) { // already parsed, too late to fix up
        logln(tree);
        fail;
      }
    }
    return res;
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
  }
  string fqn() {
    return get!(IModule).getIdentifier()~"."~name;
  }
  string cached_selfmangle;
  override string mangleSelf() {
    if (cached_selfmangle) return cached_selfmangle;
    if (name == "__c_main") {
      if (isWindoze()) { cached_selfmangle = "main_dont_use_on_this_platform"; return cached_selfmangle; }
      cached_selfmangle = "main";
      return "main";
    } else if (name == "__win_main") {
      if (platform_prefix == "i686-mingw32-") {
        // cached_selfmangle = "_WinMain@16";
        cached_selfmangle = "WinMain";
      } else {
        cached_selfmangle = "_WinMain_not_relevant_on_this_architecture";
      }
    } else if (extern_c) {
      auto res = cleaned_name;
      if (platform_prefix.find("mingw") != -1) {
        if (res == "setjmp") res = "_setjmp"; // lol wat.
      }
      cached_selfmangle = res;
    } else
      cached_selfmangle = cleaned_name~"_"~sup.mangle(null, type);
    if (cached_selfmangle.length > 252) {
      cached_selfmangle = refcompress(cached_selfmangle);
    }
    return cached_selfmangle;
  }
  string exit() { return qformat(mangleSelf(), "_exit_label"[]); }
  void addStatement(Statement st) {
    if (!tree) {
      if (auto sc = fastcast!(Scope) (st)) { tree = sc; return; }
      else {
        auto backup = namespace();
        scope(exit) namespace.set(backup);
        namespace.set(this);
        
        tree = fastalloc!(Scope)();
      }
    }
    if (!fastcast!(Scope) (tree)) {
      logln(this);
      fail;
    }
    fastcast!(Scope) (tree).addStatement(st);
  }
  void dwarfOpen(LLVMFile lf) {
    todo("Function::dwarfOpen");
    /*auto dwarf2 = lf.dwarf2;
    if (dwarf2) {
      auto sect = fastalloc!(Dwarf2Section)(
        dwarf2.cache.getKeyFor("subprogram"));
      with (sect) {
        data ~= ".byte\t0x1"; // external
        data ~= dwarf2.strings.addString(pretty_name().replace("\"", "\\\""));
        data ~= qformat(".int\t"[],
          hex(lf.getFileId(
            current_module().filename())));
        data ~= ".int\t0x0 /* line: todo * /";
        data ~= ".byte\t0x1 /* prototyped * /";
        sect.data ~= qformat(".long\t.LFB"[], idnum);
        data ~= qformat(".long\t.LFE"[], idnum);
        data ~= qformat(".byte\t1\t/* location description is one entry long * /"[]);
        data ~= qformat(".byte\t"[], hex(DW.OP_reg5), "\t/* ebp * /"[]);
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
    }*/
  }
  void dwarfClose(LLVMFile lf) {
    todo("Function::dwarfClose");
    /*if (lf.dwarf2) {
      lf.dwarf2.close;
      lf.dwarf2.close;
    }*/
  }
  string fun_start_sym() { return qformat(".LFB"[], idnum); }
  string fun_end_sym() { return qformat(".LFE"[], idnum); }
  string fun_linenr_sym() { return qformat(".DebugInfo_LineInfo"[], idnum); }
  int[] linenumbers;
  int linecounter;
  string linedebug(int id) {
    return qformat(".DebugInfo_"[], idnum, "_Line_"[], id);
  }
  void add_line_number(LLVMFile lf, int line) {
    todo("Function::add_line_number");
    /*lf.put(linedebug(linecounter++), ":"[]);
    linenumbers ~= line;*/
  }
  override {
    bool addsSelf() { return true; }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ name;
    }
    string getIdentifier() { return name; }
    void emitLLVM(LLVMFile lf) { if (once(lf, "fun "~mangleSelf())) {
      auto cef_backup = current_emitting_function();
      current_emitting_function.set(this);
      scope(exit) current_emitting_function.set(cef_backup);
      
      parseMe();
      
      if (alreadyEmat) {
        logln("tried to emit twice: ", this);
        asm { int 3; }
      }
      alreadyEmat = true;
      
      foreach (dep; dependents) dep.emitLLVM(lf);
      
      // record initial frame
      auto argframetype = frametype2(this);
      llvmFrameTypes ~= argframetype;
      
      inEmitAsm = true;
      scope(exit) inEmitAsm = false;
      
      if (lf.exprs.length) {
        logln("garbage llvm expr stack when emitting ", this, ": ", lf.exprs);
        fail;
      }
      
      auto fmn = mangleSelf(); // full mangled name
      
      // function_head is used for the definition of the stackframe
      lf.beginSection("function_head");
      scope(success) {
        auto data = lf.endSection("function_head");
        lf.put(data);
      }
      lf.beginSection("function_allocas");
      scope(success) {
        auto data = lf.endSection("function_allocas");
        lf.put(data);
      }
      auto retstr = typeToLLVM(type.ret);
      
      string argstr;
      foreach (i, arg; getParams(true)) {
        if (argstr) argstr ~= ", ";
        argstr = qformat(argstr, typeToLLVM(arg.type, true), " %arg", i);
      }
      lf.undecls[fmn] = true;
      
      string linkage, flags;
      if (weak)
        // linkage = "linkonce_odr ";
        linkage = "weak_odr ";
      if (extern_c) {
        flags ~= "noinline ";
      }
      if (name == "__fcc_main") flags ~= "noinline ";
      if (type.stdcall) linkage = "x86_stdcallcc ";
      // flags ~= "fastcc ";
      put(lf, "define ", linkage, retstr, " @", fmn, "(", argstr, ") ", flags, "{");
      scope(success) put(lf, "}");
      if (extern_c) preserve ~= ","~fmn;
      
      lf.beginSection("function");
      scope(success) {
        auto data = lf.endSection("function");
        bool[string] accounted;
        string allocsize;
        outer:foreach (type; llvmFrameTypes) {
          if (type in accounted) continue;
          // remove types that are prefix structs of another type
          if (auto mid = type.startsWith("{").endsWith("}")) {
            foreach (t2; llvmFrameTypes) if (auto m2 = t2.startsWith("{").endsWith("}")) {
              if (m2.startsWith(mid).startsWith(",")) continue outer;
            }
          }
          auto oldsize = allocsize.length;
          if (!allocsize) allocsize = lltypesize(type);
          else allocsize = llmax(allocsize, lltypesize(type));
          // else allocsize = lladd(allocsize, lltypesize(type)); // Blame LLVM for this shit
          /*if (allocsize.length != oldsize) {
            logln("+", this.name, " ", type);
          }*/
          if (allocsize.length > 1024*1024) fail;
          accounted[type] = true;
        }
        /*if (fmn == "reverse_module_std_0E_util__of_function_of_rich_auto_array_of_tuple__ref_module_gui_0E_base_Widget_int__templinst_reverse_with_rich_auto_array_of_tuple__ref_module_gui_0E_base_Widget_int") {
          logln("alloc (", cast(void*) this, ") ", readllex(allocsize), " - ", allocsize);
          logln("due to ", llvmFrameTypes);
          asm { int 3; }
        }*/
        allocsize = readllex(allocsize);
        put(lf, "%__stackframe = alloca i8, i32 ", allocsize, ", align 16");
        // fill stackframe for params
        auto stackp = bitcastptr(lf, "i8", argframetype, "%__stackframe");
        foreach (i, arg; getParams(true)) {
          auto argp = save(lf, "getelementptr inbounds ", argframetype, "* ", stackp, ", i32 0, i32 ", i);
          auto argtype = typeToLLVM(arg.type);
          auto argtype2 = typeToLLVM(arg.type, true);
          auto argpconv = bitcastptr(lf, argtype, argtype2, argp);
          put(lf, "store ", argtype2, " %arg", i, ", ", argtype2, "* ", argpconv);
        }
        lf.put(data);
      }
      
      // logln("todo dwarf");
      // dwarfOpen(lf);
      // scope(exit) dwarfClose(lf);
      
      // if (lf.profileMode)
      //   lf.put("call mcount"[]);
      
      if (!tree) { logln("Tree for ", this, " not generated! :( "); fail; }
      
      auto backupns = namespace();
      scope(exit) namespace.set(backupns);
      namespace.set(this);
      
      tree.emitLLVM(lf);
      
      if (type.ret != Single!(Void) && !extern_c) {
        funcall_emit_fun_end_guard (lf, name);
      }
      
      lf.emitLabel(exit(), true);
      
      if (type.ret == Single!(Void)) {
        put(lf, "ret void");
      } else if (extern_c) {
        put(lf, "ret ", typeToLLVM(type.ret), " zeroinitializer");
      } else {
        put(lf, "unreachable");
      }
    }}
    
    Stuple!(IType, string)[] stackframe() {
      Stuple!(IType, string)[] res;
      auto pars = getParams(true);
      foreach (arg; getParams(true)) {
        res ~= stuple(arg.type, arg.name);
      }
      foreach (obj; field)
        if (auto var = fastcast!(Variable)(obj._1)) {
          // register all vars that are not arg holders
          // this gives us the best of both worlds: it allows us to function
          // while executing fixup, and creates correct results afterwards.
          bool found;
          foreach (arg; pars)
            if (arg.name == var.name) { found = true; break; }
          if (!found)
            res ~= stuple(var.type, var.name);
        }
      return res;
    }
    Object lookup(string name, bool local = false) {
      parseMe;
      if (auto res = super.lookup(name, true)) return res;
      if (auto res = lookupInImports(name, local)) return res;
      if (local) return null;
      return super.lookup(name, local);
    }
    Extensible extend(Extensible e2) {
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
    Extensible simplify() { return this; }
  }
  Function alloc() { return fastalloc!(Function)(); }
}

void mkAbstract(Function fun) {
  fun.isabstract = true;
  if (auto that = namespace().lookup("this"[]))
    fun.addStatement(
      iparse!(Statement, "undefined_function"[], "tree.stmt"[])
            (`raise new Error "Function $this::$fun is not implemented";`, fun, "fun"[], mkString(fun.name), "this"[], that));
  else
    fun.addStatement(
      iparse!(Statement, "undefined_function"[], "tree.stmt"[])
            (`raise new Error "Function $fun is not implemented";`, fun, "fun"[], mkString(fun.toString())));
}

TLS!(Function) current_emitting_function;
static this() { New(current_emitting_function); }

class OverloadSet : Named, Extensible, Iterable {
  string name;
  Function[] funs;
  this(string n, Function[] f...) {
    name = n;
    foreach (fun; f) add(fun);
  }
  mixin defaultIterate!(funs);
  OverloadSet dup() {
    Function[] f2;
    foreach (fun; funs) f2 ~= fun.dup();
    return fastalloc!(OverloadSet)(name, f2);
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

int fc_count;
class FunCall : Expr {
  Expr[] params;
  Function fun;
  Statement setup;
  Expr[] getParams() { return params; }
  int count;
  this() { count = fc_count++; }
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
  void emitWithArgs(LLVMFile lf, Expr[] args) {
    if (setup) setup.emitLLVM(lf);
    callFunction(lf, fun.type.ret, fun.extern_c, fun.type.stdcall, args, fun.getPointer());
  }
  override void emitLLVM(LLVMFile lf) {
    emitWithArgs(lf, params);
  }
  override string toString() { return Format(count, " (", fun.name, "(", params, "))"); }
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

import tools.log, ast.fold;
void callFunction(LLVMFile lf, IType ret, bool external, bool stdcall, Expr[] params, Expr fp) {
  mixin(mustOffset("1"));
  auto fpv = save(lf, fp);
  string[] parlist;
  foreach (par; params) {
    auto pvt = par.valueType();
    auto para = typeToLLVM(pvt), parb = typeToLLVM(pvt, true);
    llcast(lf, para, parb, save(lf, par), pvt.llvmSize());
    parlist ~= qformat(parb, " ", lf.pop());
  }
  auto fptr = fastcast!(FunctionPointer)(fp.valueType());
  if (!fptr) fail;
  
  auto fptype = typeToLLVM(fptr);
  if (!fptr.no_tls_ptr && !fptr.stdcall && !fptype.endsWith("...)*")) {
    auto tlsptr = fastcast!(Expr)(namespace().lookup(tlsbase));
    if (!tlsptr) {
      logln("No TLS pointer found under ", namespace(), ", calling ", fp);
      fail;
    }
    parlist ~= qformat("i8* ", save(lf, tlsptr));
  }
  string flags;
  // if (!external) flags = "fastcc";
  if (stdcall) flags = "x86_stdcallcc";
  if (params.length == 1) {
    IType farg;
    bool shh_its_okay;
    if (fptr.args.length == 1) {
      farg = fptr.args[0].type;
    } else if (fptr.args.length == 2 && Single!(Variadic) == fptr.args[1].type) {
      shh_its_okay = true;
    } else {
      logln("calling ", fptr);
      logln("with ", params);
      fail;
    }
    if (!shh_its_okay) {
      auto ftype = typeToLLVM(farg);
      auto atype = typeToLLVM(params[0].valueType());
      if (atype != ftype) {
        logln("Mismatching types");
        logln("call: ", typeToLLVM(fp.valueType()), " ", fp.valueType());
        logln("with: ", atype, " ", params[0].valueType());
        fail;
      }
    }
  }
  auto callstr = qformat("call ", flags, " ", fptype, " ", fpv, "(", parlist.join(", "), ")");
  if (Single!(Void) == ret) {
    put(lf, callstr);
    lf.push("void");
  } else {
    load(lf, callstr);
  }
}

class FunctionType : ast.types.Type {
  IType ret;
  Argument[] params;
  bool stdcall;
  this() { }
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
  override string llvmSize() { fail; return null; }
  override string llvmType() { fail; return null; }
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

extern(C) IType resolveTup(IType, bool onlyIfChanged = false);

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
          { ptype = fastcast!(IType)(rest(t2, "type")); if (auto r2=ptype?resolveTup(ptype, true):null) ptype = r2; return test(ptype); }() || test(ptype = lastType) || allowNull
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
    static if (is(typeof(_fun()))) auto fun = _fun();
    else auto fun = _fun;
    New(fun.type);
    fun.type.ret = ret;
    fun.type.params = _params;
    fun.name = forcename?forcename:fun_name;
    fun.reassign = reassign;
    fun.sup = sup_override ? sup_override : ns;
    if (fun.name == "__win_main") {
      fun.type.stdcall = true;
      fun.extern_c = true;
    }
    auto backup = namespace();
    namespace.set(fun);
    scope(exit) namespace.set(backup);
    
    if (fun.name == "main"[]) {
      if (gotMain) {
        asm { int 3; }
        t2.failparse("Main already defined: ", gotMain);
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
      // if we have a thread pointer..
      {
        auto pars = fun.getParams(true);
        if (pars.length && pars[$-1].name == tlsbase) {
          // generate an exception record
          if (fun.tree) fail; // wat
        }
      }
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
        if (text.accept(";"[])) { // undefined function
          mkAbstract(fun);
          return fun;
        }
        fun.coarseSrc = text;
        fun.leaveFragmentText = true;
        // logln("coarse = ", text.nextText());
        fun.parseMe;
        text = fun.coarseSrc;
        // logln("skip to ", text.nextText());
        fun.coarseSrc = null;
        if (!fun.type.ret)
          fun.type.ret = Single!(Void); // implicit return
        return fun;
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
  auto fun = fastalloc!(Function)();
  fun.extern_c = ExternC;
  return gotGenericFunDef(fun, cast(Namespace) null, true, text, cont, rest);
}
mixin DefaultParser!(gotFunDef!(false), "tree.fundef"[]);
mixin DefaultParser!(gotFunDef!(true), "tree.fundef_externc"[]);

// ensuing code gleefully copypasted from nestfun
// yes I wrote delegates first. how about that.
class FunctionPointer : ast.types.Type, ExternAware {
  IType ret;
  Argument[] args;
  bool stdcall, no_tls_ptr;
  Function delayfun;
  string toString() { return Format(ret, " function("[], args, ")"[], stdcall?" stdcall":""[]); }
  this(IType ret, Argument[] args, bool no_tls_ptr = false) {
    if (!ret) fail;
    this.ret = ret;
    this.args = args.dup;
    this.no_tls_ptr = no_tls_ptr;
  }
  this(Function fun) {
    delayfun = fun;
    ret = fun.type.ret;
    args = fun.type.params.dup;
    if (fun.extern_c) no_tls_ptr = true;
  }
  override void markExternC() {
    no_tls_ptr = true;
  }
  override string llvmSize() {
    if (nativePtrSize == 4) return "4";
    if (nativePtrSize == 8) return "8";
    fail;
  }
  string ltcache;
  override string llvmType() {
    if (!ltcache) {
      if (!ret) ret = delayfun.type.ret;
      if (!ret) fail;
      ltcache = typeToLLVM(ret) ~ "(";
      foreach (i, ref arg; args) {
        if (!arg.type) arg.type = delayfun.type.params[i].type;
        if (i) ltcache ~= ", ";
        ltcache ~= typeToLLVM(arg.type, true);
      }
      // tls pointer
      if (!no_tls_ptr && !stdcall && !ltcache.endsWith("...")) {
        if (args.length) ltcache ~= ", ";
        ltcache ~= typeToLLVM(voidp, true);
      }
      
      ltcache ~= ")*";
    }
    return ltcache;
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
    
    scope arginfo = new string[args.length];
    foreach (i, arg; args) arginfo[i] = arg.type.mangle();
    string retmang = ret.mangle();
    
    qappend("fp_ret_", retmang, "_args");
    if (!args.length) qappend("_none");
    else foreach (arg; arginfo) {
      qappend("_", arg);
    }
    auto res = qfinalize();
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
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    fun.iterate(dg, IterMode.Semantic);
  }
  IType typecache;
  override {
    override FunRefExpr dup() { return fastalloc!(FunRefExpr)(fun); }
    IType valueType() {
      if (!typecache) typecache = fastalloc!(FunctionPointer)(fun);
      return typecache;
    }
    void emitLLVM(LLVMFile lf) {
      auto c = new FunSymbol(fun);
      c.emitLLVM(lf);
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
      return fastalloc!(FunctionPointer)(cur, list.dup);
    } else return null;
  };
}
