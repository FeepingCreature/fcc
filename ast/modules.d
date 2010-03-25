module ast.modules;

import ast.base, ast.namespace, ast.fun, ast.variable;

import tools.ctfe, tools.base: startsWith;

class Module : Namespace, Tree {
  string name;
  Module[] imports;
  Tree[] entries;
  override {
    void emitAsm(AsmFile af) {
      foreach (entry; entries)
        entry.emitAsm(af);
    }
    string mangle(string name, Type type) {
      return "module_"~this.name~"_"~name~"_of_"~type.mangle();
    }
    template Kind(T, string Name) {
      mixin(`
        T lookup$NAME(string name) {
          if (auto res = super.lookup$NAME(name)) return res;
          if (auto lname = name.startsWith(this.name~"."))
            if (auto res = super.lookup$NAME(lname)) return res;
          foreach (mod; imports)
            if (auto res = mod.lookup$NAME(name)) return res;
          return null;
        }
        `.ctReplace("$NAME", Name));
    }
    mixin Kind!(Class, "Class");
    mixin Kind!(Function, "Fun");
    mixin Kind!(Variable, "Var");
  }
}

Module sysmod;

Module lookupMod(string name) {
  if (name == "sys") {
    return sysmod;
  }
  assert(false, "TODO");
}

static this() {
  New(sysmod);
  sysmod.name = "sys";
  {
    auto puts = new Function;
    puts.extern_c = true;
    New(puts.type);
    puts.type.ret = tmemo(new Void);
    puts.type.params ~= stuple(tmemo(new Pointer(new Char)), cast(string) null);
    puts.name = "puts";
    sysmod.addFun(puts);
  }
  
  {
    auto printf = new Function;
    printf.extern_c = true;
    New(printf.type);
    printf.type.ret = tmemo(new Void);
    printf.type.params ~= stuple(tmemo(new Pointer(new Char)), cast(string) null);
    printf.type.params ~= stuple(tmemo(new Variadic), cast(string) null);
    printf.name = "printf";
    sysmod.addFun(printf);
  }
}
