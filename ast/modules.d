module ast.modules;

import cache, ast.base, ast.namespace, ast.parse, ast.fold, ast.fun;

import tools.ctfe, tools.threadpool;

bool dumpXMLRep;

Threadpool tp;

pragma(set_attribute, check_imports_usage, externally_visible);
extern(C) void check_imports_usage(string info, Namespace[] imports, bool[] importsUsed) {
  foreach (i, ns; imports) if (auto mod = fastcast!(Module) (ns)) {
    // importing module with constructor can be valid reason to import never-used module.
    if (!mod.constrs.length && !*getPtrResizing(importsUsed, i))
      logSmart!(false)("WARN:"[], info, ": import "[], mod.name, " never used. "[]);
  }
}

import memconserve_stdfile;
alias memconserve_stdfile.exists exists;

class Module : NamespaceImporter, IModule, Tree, Named, StoresDebugState, EmittingContext {
  string name;
  string sourcefile;
  string cleaned_name() { return name.cleanup(); }
  mixin ImporterImpl!();
  Function[] constrs;
  Tree[] entries;
  Setupable[] setupable;
  bool parsingDone;
  LLVMFile inProgress; // late to the party;
  bool _hasDebug = true;
  Module[] imports_cache;
  Module[] getAllModuleImports() {
    if (imports_cache) return imports_cache;
    
    auto backup = current_module();
    scope(exit) current_module.set(backup);
    current_module.set(this);
    
    if (sourcefile) {
      string relevant_file = sourcefile;
      if (sourcefile == "sys.nt") relevant_file = "fcc.exe";
      if (auto cache = read_cache("module imports", relevant_file)) {
        Module[] res;
        bool failed;
        while (cache) {
          auto entry = slice(cache, ",");
          try res ~= lookupMod(entry);
          catch (Exception ex) { failed = true; break; } // don't use cache if it leads to errors
        }
        if (!failed) {
          imports_cache = res;
          return res;
        }
      }
    }
    
    Module[] res;
    res ~= fastcast!(Module) (sysmod);
    foreach (ns; getImports())
      if (auto mod = fastcast!(Module) (ns))
        res ~= mod;
    int i;
    // don't foreach!
    // getImports may parseme, may add more entries.
    while (i < entries.length) {
      auto entry = entries[i++];
      if (auto imp = fastcast!(Importer) (entry))
        foreach (ns; imp.getImports())
          if (auto mod = fastcast!(Module) (ns))
            res ~= mod;
    }
    
    if (sourcefile) {
      string[] names;
      foreach (entry; res) names ~= entry.name;
      string relevant_file = sourcefile;
      if (sourcefile == "sys.nt") relevant_file = "fcc.exe";
      write_cache("module imports", relevant_file, names.join(","));
    }
    
    imports_cache = res;
    return res;
  }
  bool isValid; // still in the build list; set to false if superceded by a newer Module
  bool doneEmitting, alreadyEmat; // one for the parser, the other for the linker
  bool dontEmit; // purely definitions, no symbols; nothing to actually compile. for instance: C modules.
  override bool getDontEmit() { return dontEmit; } // IModule workaround
  override bool getDoneEmitting() { return doneEmitting; } // same
  bool splitIntoSections;
  private this() { assert(false); }
  this(string name, string sourcefile) {
    this.name = name;
    this.sourcefile = sourcefile;
    //                      needed by sysmod; avoid circle
    isValid = true;
  }
  override string filename() { return sourcefile; }
  override string modname() { return name; }
  void addSetupable(Setupable s) {
    setupable ~= s;
    if (inProgress) s.setup(inProgress);
  }
  override {
    void addEntry(Tree tr) {
      if (doneEmitting) {
        logln("Internal compiler error: cannot add to ", name, ", already emat: ", tr);
        asm { int 3; }
      }
      entries ~= tr;
    }
    bool isBeingEmat() { return !!inProgress; }
    void _add(string name, Object obj) {
      if (auto fn = fastcast!(Function)(obj)) {
        if (fn.name == "init"[]) {
          fn.sup = this;
          fn.name = qformat("init", constrs.length);
          constrs ~= fn;
          return;
        }
      }
      super._add(name, obj);
    }
    bool hasDebug() { return _hasDebug; }
    void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
      if (mode == IterMode.Semantic) fail; // what
      auto backup = current_module();
      scope(exit) current_module.set(backup);
      current_module.set(this);
      defaultIterate!(entries).iterate(dg);
    }
    mixin defaultCollapse!();
    Module dup() { assert(false, "What the hell are you doing, man. "[]); }
    string getIdentifier() { return name; }
    void emitLLVM(LLVMFile lf) {
      lf.beginSection("module");
      put(lf, `target datalayout = "`, datalayout, `"`);
      if (platform_prefix) {
        auto triple = platform_prefix[0..$-1];
        auto parts = triple.split("-");
        if (parts.length == 2) triple = qformat(parts[0], "-pc-", parts[1]);
        put(lf, `target triple = "`, triple, `"`);
      } else {
        put(lf, `target triple = "i386-pc-linux-gnu"`);
      }
      put(lf, `%size_t = type i32`);
      // put(lf, `!0 = metadata !{ float 2.5 } ; maximum acceptable inaccuracy in a float op tagged with !0`);
      scope(success) {
        auto tlsbase = qformat("_sys_tls_data_", name.replace(".", "_").replace("-", "_dash_"));
        put(lf, "@", tlsbase, "_start = global i8 0, section \"tlsvars\"");
        if (name == "sys") {
          put(lf, `@_sys_tls_data_start = global i8 0, section "tlsvars"`);
          lf.undecls["_sys_tls_data_start"] = true;
        }
        if ("tlsdefs" in lf.sectionStore) {
          lf.put(lf.sectionStore["tlsdefs"]);
          lf.sectionStore.remove("tlsdefs"); 
        }
        put(lf, "@", tlsbase, "_end   = global i8 0, section \"tlsvars\"");
        lf.undecls[qformat(tlsbase, "_start")] = true;
        lf.undecls[qformat(tlsbase, "_end"  )] = true;
        foreach (key, value; lf.decls) {
          if (!(key in lf.undecls)) {
            put(lf, value);
          }
        }
      }
      
      auto backup = current_module();
      scope(exit) current_module.set(backup);
      current_module.set(this);
      inProgress = lf;
      foreach (s; setupable) s.setup(lf);
      scope(exit) inProgress = null;
      
      int i; // NOTE: not a foreach! entries may yet grow.
      while (i < entries.length) {
        auto entry = entries[i++];
        // logln("emit entry "[], entry);
        if (fastcast!(NoOp) (entry)) continue;
        opt(entry);
        entry.emitLLVM(lf);
      }
      
      if (lf.debugmode_dwarf) {
        auto zero = addMetadata(lf, "i32 0");
        auto subproglist = addMetadata(lf, lf.dwarf_subprogs.join(", ")); 
        auto dsourcefile = sourcefile; // debug sourcefile
        if (!dsourcefile.length) dsourcefile = "fuckllvmanditsretardedinterpretationofquotecorrectunquotedwarf.nt"; 
        
        put(lf, "!llvm.dbg.cu = !{", addMetadata(lf,
          "i32 786449, "
          "metadata ", addMetadata(lf, `metadata !"`, dsourcefile.filenamepart(), `",  metadata !"`, dsourcefile.dirpart(), `"`), `, `,
          `i32 2, metadata !"fcc", i1 false, metadata !"", i32 0`
          `, metadata `, zero, `, metadata `, zero, `, metadata `, subproglist,
          `, metadata `, zero, `, metadata `, zero, `, metadata !""`), "}");
      }
      // if (!isARM) lf.put(".section .text"[]);
      doneEmitting = true;
      checkImportsUsage;
    }
    string mangle(string name, IType type) {
      return qformat("module_"[], cleaned_name(), "_"[], name.cleanup(), type?qformat("_of_"[], type.mangle()):""[]);
    }
    Object lookup(string name, bool local = false) {
      if (auto res = super.lookup(name)) return res;
      
      if (auto lname = parseBase.startsWith(parseBase.startsWith(name, this.name), "."))
        if (auto res = super.lookup(lname)) return res;
      
      return lookupInImports(name, local);
    }
    string toString() { return "module "~name~(alreadyEmat?" [done]":""); }
  }
}

static this() {
  registerSetupable = (Setupable s) { (fastcast!(Module) (current_module())).addSetupable(s); };
}

pragma(set_attribute, __getSysmod, externally_visible);
extern(C) Namespace __getSysmod() { return sysmod; } // for ast.namespace

Module[string] modcache;

Lock cachelock; // also covers currentlyParsing
bool[string] currentlyParsing;

static this() { New(cachelock); }

// some module names may require special handling
// for instance, c.*
Module delegate(string) specialHandler;

TLS!(IType) RefToParentType;
TLS!(Expr delegate(Expr refexpr)) RefToParentModify;

static this() {
  New(RefToParentType, delegate IType() { return null; });
  New(RefToParentModify, delegate Expr delegate(Expr) *() {
    return &(new Stuple!(Expr delegate(Expr)))._0;
  });
}

import tools.base: read, castLike, sub;
string[] module_stack;
Module[string] modules_wip;
Module lookupMod(string name) {
  // reset for in-member function imports
  auto rtpt_backup = RefToParentType();
  scope(exit) RefToParentType.set(rtpt_backup);
  RefToParentType.set(null);
  
  foreach (i, mod; module_stack) {
    if (mod == name) {
      string loop() {
        auto parts = module_stack[i..$];
        string res;
        void add(string s) {
          if (res.length) res ~= " -> ";
          res ~= s;
        }
        foreach (part; parts) add(part);
        add(name);
        return res;
      }
      logln("WARN: module loop "[], loop(), ". This is not well tested. "[]);
      return modules_wip[name];
    }
  }
  module_stack ~= name;
  scope(exit) module_stack = module_stack[0..$-1];
  if (name == "sys"[]) {
    return fastcast!(Module) (sysmod);
  }
  Module res;
  cachelock.Synchronized = {
    while (true) {
      if (name in currentlyParsing) {
        cachelock.Unsynchronized = { slowyield(); };
        continue;
      }
      break;
    }
    if (auto p = name in modcache) {
      res = *p;
      return;
    }
    currentlyParsing[name] = true;
  };
  if (res) return res;
  
  scope(exit) cachelock.Synchronized = {
    currentlyParsing.remove(name);
  };
  Module mod;
  auto fn = (name.replace("."[], "/"[]) ~ EXT);
  if (specialHandler) mod = specialHandler(name);
  if (!mod) {
    if (!fn.exists()) {
      foreach (path; include_path) {
        auto combined = path.sub(fn);
        if (combined.exists()) {
          fn = combined;
          break;
        }
      }
    }
    if (!fn.exists()) {
      throw new Exception("No such module: "~name);
    }
    auto file = fn.read().castLike(""[]);
    synchronized(SyncObj!(sourcefiles))
      sourcefiles[fn] = file;
    mod = fastcast!(Module) (parse(file, "tree.module"[]));
    if (!mod)
      file.failparse("Could not parse module");
    if (file.strip().length)
      file.failparse("Failed to parse module");
  }
  cachelock.Synchronized = {
    modcache[name] = mod;
  };
  return mod;
}

string[string] locatecache;
string locate_name(string name) {
  string res;
  cachelock.Synchronized = {
    if (auto p = name in locatecache) res = *p;
    else {
      foreach (key, value; modcache) {
        if (value.lookup(name, true)) { if (res.length) res ~= ", "; res ~= key; }
      }
      locatecache[name] = res;
    }
  };
  return res;
}

void unknownId(string id, string text, bool fail = false) {
  string msg;
  if (auto hint = locate_name(id)) {
    msg = qformat("unknown identifier: '", id, "', appears in ", hint);
  } else {
    msg = qformat("unknown identifier: '", id, "'");
  }
  if (fail) {
    // asm { int 3; }
    resetError();
    text.failparse(msg);
  } else text.setError(msg);
}
