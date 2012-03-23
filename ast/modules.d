module ast.modules;

import ast.base, ast.namespace, ast.parse, ast.fold, ast.fun;

import tools.ctfe, tools.threadpool;

alias asmfile.startsWith startsWith;

string[] include_path;

bool dumpXMLRep;

static this() {
  include_path ~= "/usr/local/include";
  include_path ~= "/usr/include";
}

Threadpool tp;

extern(C) void check_imports_usage(string info, Namespace[] imports, bool[] importsUsed) {
  foreach (i, ns; imports) if (auto mod = fastcast!(Module) (ns)) {
    // importing module with constructor can be valid reason to import never-used module.
    if (!mod.constrs.length && !*getPtrResizing(importsUsed, i))
      logSmart!(false)("WARN:", info, ": import ", mod.name, " never used. ");
  }
}

class Module : NamespaceImporter, IModule, Tree, Named, StoresDebugState, EmittingContext {
  string name;
  string sourcefile;
  string cleaned_name() { return name.cleanup(); }
  mixin ImporterImpl!();
  Function[] constrs;
  Tree[] entries;
  Setupable[] setupable;
  bool parsingDone;
  AsmFile inProgress; // late to the party;
  bool _hasDebug = true;
  Module[] getAllModuleImports() {
    Module[] res;
    res ~= fastcast!(Module) (sysmod);
    foreach (ns; getImports())
      if (auto mod = fastcast!(Module) (ns))
        res ~= mod;
    foreach (entry; entries)
      if (auto imp = fastcast!(Importer) (entry))
        foreach (ns; imp.getImports())
          if (auto mod = fastcast!(Module) (ns))
            res ~= mod;
    return res;
  }
  bool isValid; // still in the build list; set to false if superceded by a newer Module
  bool doneEmitting, alreadyEmat; // one for the parser, the other for the linker
  bool dontEmit; // purely definitions, no symbols; nothing to actually compile.
  bool splitIntoSections;
  private this() { assert(false); }
  this(string name, string sourcefile) {
    this.name = name;
    this.sourcefile = sourcefile;
    //                      needed by sysmod; avoid circle
    isValid = true;
  }
  override string filename() { return name.replace(".", "/") ~ EXT; }
  override string modname() { return name; }
  void addSetupable(Setupable s) {
    setupable ~= s;
    if (inProgress) s.setup(inProgress);
  }
  override {
    bool isBeingEmat() { return !!inProgress; }
    void _add(string name, Object obj) {
      if (auto fn = fastcast!(Function)(obj)) {
        if (fn.name == "init") {
          fn.sup = this;
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
    Module dup() { assert(false, "What the hell are you doing, man. "); }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      auto backup = current_module();
      scope(exit) current_module.set(backup);
      current_module.set(this);
      inProgress = af;
      foreach (s; setupable) s.setup(af);
      scope(exit) inProgress = null;
      
      int i; // NOTE: not a foreach! entries may yet grow.
      while (i < entries.length) {
        auto entry = entries[i++];
        // logln("emit entry ", entry);
        if (fastcast!(NoOp) (entry)) continue;
        // globvars don't write any code!
        // keep our assembly clean. :D
        if ((fastcast!(Object) (entry)).classinfo.name != "ast.globvars.GlobVarDecl" && splitIntoSections) {
          auto codename = Format("index_", i);
          if (auto mang = fastcast!(IsMangled) (entry)) codename = mang.mangleSelf();
          if (isWindoze())
            af.put(".section .text.", codename, ", \"ax\"");
          else if (isARM)
            {}
          else
            af.put(".section .text.", codename, ", \"ax\", @progbits");
        }
        opt(entry);
        entry.emitAsm(af);
      }
      if (!isARM) af.put(".section .text");
      doneEmitting = true;
      checkImportsUsage;
    }
    string mangle(string name, IType type) {
      return "module_"~cleaned_name()~"_"~name.cleanup()~(type?("_of_"~type.mangle()):"");
    }
    Object lookup(string name, bool local = false) {
      if (auto res = super.lookup(name)) return res;
      
      if (auto lname = name.startsWith(this.name).startsWith("."))
        if (auto res = super.lookup(lname)) return res;
      
      return lookupInImports(name, local);
    }
    string toString() { return "module "~name; }
  }
  override Stuple!(IType, string, int)[] stackframe() { assert(false); }
}

static this() {
  registerSetupable = (Setupable s) { (fastcast!(Module) (current_module())).addSetupable(s); };
}

extern(C) Namespace __getSysmod() { return sysmod; } // for ast.namespace

Module[string] cache;

Lock cachelock; // also covers currentlyParsing
bool[string] currentlyParsing;

static this() { New(cachelock); }

bool delegate(Module) rereadMod;
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

import tools.compat: read, castLike, exists, sub;
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
      logln("WARN: module loop ", loop(), ". This is not well tested. ");
      return modules_wip[name];
    }
  }
  module_stack ~= name;
  scope(exit) module_stack = module_stack[0..$-1];
  if (name == "sys") {
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
    if (auto p = name in cache) {
      // return *p; // BAD!
      if (!rereadMod || !rereadMod(*p)) {
        res = *p;
        return;
      }
    }
    currentlyParsing[name] = true;
  };
  if (res) return res;
  
  scope(exit) cachelock.Synchronized = {
    currentlyParsing.remove(name);
  };
  Module mod;
  auto fn = (name.replace(".", "/") ~ EXT);
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
    if (!fn.exists()) return null;
    auto file = fn.read().castLike("");
    synchronized(SyncObj!(sourcefiles))
      sourcefiles[fn] = file;
    mod = fastcast!(Module) (parsecon.parse(file, "tree.module"));
    if (!mod)
      file.failparse("Could not parse module");
    if (file.strip().length)
      file.failparse("Failed to parse module");
  }
  cachelock.Synchronized = {
    cache[name] = mod;
  };
  return mod;
}
