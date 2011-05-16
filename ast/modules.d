module ast.modules;

import ast.base, ast.namespace, ast.fun, ast.parse, ast.structure;

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
  string cleaned_name() { return name.cleanup(); }
  Module[] imports, public_imports;
  Module[] getImports() { return imports ~ public_imports; }
  bool[] importsUsed; // print warnings on unused imports (but NOT public ones!)
  static bool* getPtrResizing(ref bool[] array, int offs) {
    if (array.length <= offs) array.length = offs + 1;
    return &array[offs];
  }
  void checkImportsUsage() {
    foreach (i, mod; imports) {
      // importing module with constructor can be valid reason to import never-used module.
      if (!mod.constrs.length && !*getPtrResizing(importsUsed, i))
        logln("WARN:", name, ": import ", mod.name, " never used. ");
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
  private this() { assert(false); }
  this(string name) {
    this.name = name;
    //                      needed by sysmod; avoid circle
    isValid = true;
  }
  string filename() { return name.replace(".", "/") ~ ".cr"; }
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
    void iterate(void delegate(ref Iterable) dg) {
      auto backup = current_module();
      scope(exit) current_module.set(backup);
      current_module.set(this);
      defaultIterate!(entries).iterate(dg);
    }
    Module dup() { assert(false, "What the hell are you doing, man. "); }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      checkImportsUsage;
      auto backup = current_module();
      scope(exit) current_module.set(backup);
      current_module.set(this);
      inProgress = af;
      foreach (s; setupable) s.setup(af);
      scope(exit) inProgress = null;
      int i; // NOTE: not a foreach! entries may yet grow.
      while (i < entries.length) {
        auto entry = entries[i++];
        entry.emitAsm(af);
      }
      void callback(ref Iterable it) {
        if (cast(NoOp) it) return;
        string info = Format("<node classname=\"", (fastcast!(Object)~ it).classinfo.name, "\"");
        if (auto n = fastcast!(Named)~ it)
          info ~= Format(" name=\"", n.getIdentifier(), "\"");
        if (auto i = cast(HasInfo) it)
          info ~= Format( " info=\"", i.getInfo(), "\"");
        info ~= " >";
        logln(info);
        it.iterate(&callback);
        logln("</node>");
      }
      if (dumpXMLRep) {
        logln("----module ", name);
        iterate(&callback);
        logln("----done");
      }
      doneEmitting = true;
    }
    string mangle(string name, IType type) {
      return "module_"~cleaned_name()~"_"~name.cleanup()~(type?("_of_"~type.mangle()):"");
    }
    Object lookup(string name, bool local = false) {
      if (auto res = super.lookup(name)) return res;
      
      if (auto lname = name.startsWith(this.name).startsWith("."))
        if (auto res = super.lookup(lname)) return res;
      
      foreach (i, mod; public_imports)
        if (auto res = mod.lookup(name, true))
          return res;
      
      if (local) return null;
      
      foreach (i, mod; imports) {
        if (auto res = mod.lookup(name, true)) {
          *getPtrResizing(importsUsed, i) = true;
          return res;
        }
      }
      
      if (sysmod && sysmod !is this && name != "std.c.setjmp")
        if (auto res = sysmod.lookup(name, true)) return res;
      
      return null;
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
Module lookupMod(string name) {
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
  auto fn = (name.replace(".", "/") ~ ".cr");
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
