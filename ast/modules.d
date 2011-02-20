module ast.modules;

import ast.base, ast.namespace, ast.structure, ast.parse, ast.fun;

import tools.ctfe, tools.threads, tools.threadpool;

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
  Module[] imports;
  Function[] constrs;
  Tree[] entries;
  Setupable[] setupable;
  bool parsingDone;
  AsmFile inProgress; // late to the party;
  bool _hasDebug = true;
  bool isValid; // still in the build list; set to false if superceded by a newer Module
  private this() { assert(false); }
  this(string name) {
    this.name = name;
    //                      needed by sysmod; avoid circle
    if (sysmod && sysmod !is this && name != "std.c.setjmp")
      imports ~= sysmod;
    isValid = true;
  }
  void addSetupable(Setupable s) {
    setupable ~= s;
    if (inProgress) s.setup(inProgress);
  }
  override {
    bool hasDebug() { return _hasDebug; }
    void iterate(void delegate(ref Iterable) dg) {
      auto backup = current_module();
      scope(exit) current_module.set(backup);
      current_module.set(this);
      defaultIterate!(imports, entries).iterate(dg);
    }
    Module dup() { assert(false, "What the hell are you doing, man. "); }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      auto backup = current_module();
      current_module.set(this);
      scope(exit) current_module.set(backup);
      inProgress = af;
      foreach (s; setupable) s.setup(af);
      scope(exit) inProgress = null;
      int i; // NOTE: not a foreach! entries may yet grow.
      while (i < entries.length) {
        auto entry = entries[i++];
        /*if (auto fun = fastcast!(Function)~ entry) {
          logln("emit![", i - 1, "/", entries.length, "]: ", fun.name, " in ", cast(void*) this);
        }*/
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
    }
    string mangle(string name, IType type) {
      return "module_"~cleaned_name()~"_"~name~(type?("_of_"~type.mangle()):"");
    }
    Object lookup(string name, bool local = false) {
      if (auto res = super.lookup(name)) return res;
      if (auto lname = name.startsWith(this.name~"."))
        if (auto res = super.lookup(lname)) return res;
      
      if (local) return null;
      foreach (mod; imports) {
        if (auto res = mod.lookup(name, true)) return res;
      }
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

// extras == stuff added by the compiler
Module sysmod, extras;
static this() {
  addExtra = delegate void(IsMangled im) {
    auto mangled = im.mangleSelf();
    foreach (ref entry; extras.entries) {
      if (auto im2 = cast(IsMangled) entry)
        if (im2.mangleSelf() == mangled) {
          entry = fastcast!(Tree)~ im;
          if (auto s = fastcast!(Setupable)~ im)
            extras.addSetupable(s);
          return;
        }
    }
    extras.entries ~= fastcast!(Tree)~ im;
    if (auto s = fastcast!(Setupable)~ im)
      extras.addSetupable(s);
  };
}

extern(C) Namespace __getSysmod() { return sysmod; } // for ast.namespace

Module[string] cache;

Lock cachelock; // also covers currentlyParsing
bool[string] currentlyParsing;

static this() { New(cachelock); }

bool delegate(string) rereadMod;

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
      if (!rereadMod || !rereadMod(name)) {
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
  auto fn = (name.replace(".", "/") ~ ".cr");
  if (!fn.exists()) {
    foreach (path; include_path) {
      auto combined = path.sub(fn);
      if (combined.exists()) {
        fn = combined;
        break;
      }
    }
  }
  // logln("read ", fn);
  auto file = fn.read().castLike("");
  synchronized(SyncObj!(sourcefiles))
    sourcefiles[fn] = file;
  auto mod = fastcast!(Module)~ parsecon.parse(file, "tree.module");
  if (!mod)
    file.failparse("Could not parse module");
  if (file.strip().length)
    file.failparse("Failed to parse module");
  cachelock.Synchronized = {
    cache[name] = mod;
  };
  return mod;
}

Object gotImport(ref string text, ParseCb cont, ParseCb rest) {
  string m;
  // import a, b, c;
  auto mod = current_module();
  string[] newImports;
  if (!(
    text.bjoin(text.gotIdentifier(m, true), text.accept(","),
    { newImports ~= m; },
    true) &&
    text.accept(";")
  )) text.failparse("Unexpected text while parsing import statement");
  foreach (str; newImports)
    mod.imports ~= lookupMod(str);
  return Single!(NoOp);
}
mixin DefaultParser!(gotImport, "tree.import", null, "import");

Object gotModule(ref string text, ParseCb cont, ParseCb restart) {
  auto t2 = text;
  Structure st;
  Tree tr;
  Module mod;
  auto backup = namespace.ptr();
  scope(exit) namespace.set(backup);
  string modname;
  if (!t2.gotIdentifier(modname, true) || !t2.accept(";"))
    t2.failparse("Failed to parse module header, 'module' expected! ");
  
  New(mod, modname);
  namespace.set(mod);
  auto backup_mod = current_module();
  current_module.set(mod);
  scope(exit) current_module.set(backup_mod);
  
  if (mod.name == "sys") {
    sysmod = mod; // so that internal lookups work
  }
  if (t2.many(
      !!restart(t2, "tree.toplevel", &tr),
      {
        if (auto n = fastcast!(Named)~ tr)
          if (!addsSelf(tr))
            mod.add(n);
        mod.entries ~= tr;
      }
    )
  ) {
    eatComments(t2);
    text = t2;
    if (text.strip().length)
      text.failparse("Unknown statement");
    mod.parsingDone = true;
    return mod;
  } else t2.failparse("Failed to parse module");
}
mixin DefaultParser!(gotModule, "tree.module", null, "module");

Object gotRename(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Named n;
  string id2;
  if (!rest(t2, "tree.expr.named", &n)
    ||!t2.gotIdentifier(id2)) {
    t2.failparse("Couldn't get parameter for rename");
  }
  auto ns = namespace();
  auto id1 = n.getIdentifier(), p = id1 in ns.field_cache;
  if (!p) {
    t2.failparse("Cannot rename non-locally, use expression alias instead");
  }
  if (!t2.accept(";"))
    t2.failparse("Expected trailing semicolon in rename! ");
  auto pd = *p;
  ns.field_cache.remove(id1);
  ns.field_cache[id2] = pd;
  ns.rebuildField();
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotRename, "tree.toplevel.rename", null, "RenameIdentifier");

