module ast.modules;

import ast.base, ast.namespace, ast.fun, ast.parse;

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
  Module[] imports;
  Function[] constrs;
  Tree[] entries;
  Setupable[] setupable;
  bool parsingDone;
  AsmFile inProgress; // late to the party;
  bool _hasDebug = true;
  bool isValid; // still in the build list; set to false if superceded by a newer Module
  bool doneEmitting;
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
      auto backup = current_module();
      scope(exit) current_module.set(backup);
      current_module.set(this);
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
      doneEmitting = true;
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

// extras == stuff added by the compiler
Module sysmod, extras;
static this() {
  addExtra = delegate void(IsMangled im) {
    auto mangled = im.mangleSelf();
    if (extras.doneEmitting) {
      logln("Too late to add ", im, ": extras already emitted! ");
      asm { int 3; }
    }
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
