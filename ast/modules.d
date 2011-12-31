module ast.modules;

import ast.base, ast.namespace, ast.parse, ast.fold, ast.fun;

import tools.ctfe, tools.threadpool;

alias asmfile.startsWith startsWith;

string[] include_path;

bool dumpXMLRep;

static this() {
  include_path ~= "/usr/include";
}

Threadpool tp;

class Module : Namespace, Tree, Named, StoresDebugState {
  string name;
  string sourcefile;
  string cleaned_name() { return name.cleanup(); }
  Module[] imports, public_imports, static_imports;
  Module[] getImports() { return imports ~ public_imports ~ static_imports; }
  bool[] importsUsed; // print warnings on unused imports (but NOT public ones!)
  static bool* getPtrResizing(ref bool[] array, int offs) {
    if (array.length <= offs) array.length = offs + 1;
    return &array[offs];
  }
  void checkImportsUsage() {
    foreach (i, mod; imports) {
      // importing module with constructor can be valid reason to import never-used module.
      if (!mod.constrs.length && !*getPtrResizing(importsUsed, i))
        logSmart!(false)("WARN:", name, ": import ", mod.name, " never used. ");
    }
  }
  Function[] constrs;
  Tree[] entries;
  Setupable[] setupable;
  bool parsingDone;
  AsmFile inProgress; // late to the party;
  bool _hasDebug = true;
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
  string filename() { return name.replace(".", "/") ~ EXT; }
  void addSetupable(Setupable s) {
    setupable ~= s;
    if (inProgress) s.setup(inProgress);
  }
  override {
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
      
      Object res;
      void addres(Object obj) {
        if (!res) { res = obj; return; }
        auto ex = fastcast!(Extensible) (res), ex2 = fastcast!(Extensible)(obj);
        if (ex && !ex2 || !ex && ex2) {
          throw new Exception(Format("While looking up ", name, ": ambiguity between ",
            res, " and ", obj, ": one is overloadable and the other isn't"));
        }
        if (!ex) return;
        res = fastcast!(Object) (ex.extend(ex2));
      }
      void finalize() {
        auto xt = fastcast!(Extensible) (res);
        if (!xt) return;
        if (auto simp = xt.simplify()) res = fastcast!(Object) (simp);
      }

      foreach (mod; public_imports)
        if (auto res = mod.lookup(name, true))
          addres(res);
      
      foreach (mod; static_imports) {
        if (auto lname = name.startsWith(mod.name).startsWith(".")) {
          if (auto res = mod.lookup(lname)) return res;
        }
      }
      
      if (local) { finalize; return res; }
      
      foreach (i, mod; imports) {
        if (auto res = mod.lookup(name, true)) {
          *getPtrResizing(importsUsed, i) = true;
          addres(res);
        }
      }
      
      if (sysmod && sysmod !is this && name != "std.c.setjmp")
        if (auto res = sysmod.lookup(name, true))
          addres(res);
      
      finalize;
      return res;
    }
    string toString() { return "module "~name; }
  }
  override Stuple!(IType, string, int)[] stackframe() { assert(false); }
}

TLS!(Module) current_module;

static this() {
  registerSetupable = (Setupable s) { current_module().addSetupable(s); };
}

Module sysmod;

extern(C) Namespace __getSysmod() { return sysmod; } // for ast.namespace

Module[string] cache;

Lock cachelock; // also covers currentlyParsing
bool[string] currentlyParsing;

static this() { New(cachelock); }

bool delegate(Module) rereadMod;
// some module names may require special handling
// for instance, c.*
Module delegate(string) specialHandler;

import tools.compat: read, castLike, exists, sub;
string[] module_stack;
Module[string] modules_wip;
Module lookupMod(string name) {
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
    return sysmod;
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
