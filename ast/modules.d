module ast.modules;

import ast.base, ast.namespace, ast.fun, ast.variable, ast.structure, ast.parse;

import tools.ctfe;

class Module : Namespace, Tree, Named {
  string name;
  Module[] imports;
  Tree[] entries;
  mixin defaultIterate!(imports, entries);
  override {
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      foreach (entry; entries)
        entry.emitAsm(af);
    }
    string mangle(string name, IType type) {
      return "module_"~this.name~"_"~name~(type?("_of_"~type.mangle()):"");
    }
    Object lookup(string name, bool local = false) {
      if (auto res = super.lookup(name)) return res;
      if (auto lname = name.startsWith(this.name~"."))
        if (auto res = super.lookup(lname)) return res;
      
      foreach (mod; imports)
        if (auto res = mod.lookup(name)) return res;
      return null;
    }
  }
  override Stuple!(IType, string, int)[] stackframe() { assert(false); }
}

Module sysmod;

extern(C) Namespace __getSysmod() { return sysmod; } // for ast.namespace
Module lookupMod(string name) {
  if (name == "sys") {
    return sysmod;
  }
  assert(false, "TODO");
}

import ast.pointer;
// not static this() to work around a precedence bug in phobos. called from fcc.
void setupSysmods() {
  string src = `
    module sys;
    extern(C) {
      void puts(char*);
      void printf(char*, ...);
      void* malloc(int);
      void* calloc(int, int);
      void free(void*);
      void* realloc(void* ptr, size_t size);
      void* memcpy(void* dest, void* src, int n);
      int snprintf(char* str, int size, char* format, ...);
    }
    context mem {
      void* delegate(int)            malloc_dg = &malloc;
      void* delegate(int, int )      calloc_dg = &calloc;
      void delegate(void*)             free_dg = &free;
      void* delegate(void*, size_t) realloc_dg = &realloc;
      void* malloc (int i)             { return malloc_dg(i); }
      void* calloc (int i, int k)      { return calloc_dg(i, k); }
      void  free   (void* p)           { free_dg(p); }
      void* realloc(void* p, size_t s) { return realloc_dg(p, s); }
      /*MARKER*/
      void append(char[] target, char[] text) {
        int newsize = target.length + text.length;
        char[] newtarget;
        if newsize <= target.capacity newtarget = target;
        else {
          newtarget = new(newsize) char;
          newtarget[0 .. target.length] = target;
        }
        newtarget[target.length .. newsize] = text;
      }
    }
    char[] itoa(int i) {
      if i < 0 return "-" ~ itoa(-i);
      if i == 0 return "0";
      char[] res;
      while i {
        char[1] temp;
        temp[0] = "0123456789"[i%10];
        res = temp ~ res;
        i = i / 10;
      }
      return res;
    }
    char[] ptoa(void* p) {
      auto res = new(size_t.sizeof * 2 + 2 + 1) char;
      snprintf(res.ptr, res.length, "%p", p);
      return res[0 .. res.length - 1];
    }
    void writeln(char[] line) {
      printf("%.*s\n", line.length, line.ptr);
    }
  `;
  // parse first half
  string base = src.between("", "/*MARKER*/") ~ "}";
  sysmod = cast(Module) parsecon.parse(base, "tree.module");
  // parse complete
  sysmod = cast(Module) parsecon.parse(src, "tree.module");
}

import tools.log;
Object gotExtern(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("extern(C)")) return null;
  bool grabFun() {
    auto fun = new Function;
    fun.extern_c = true;
    New(fun.type);
    if (test(fun.type.ret = cast(IType) rest(t2, "type")) &&
        t2.gotIdentifier(fun.name) &&
        t2.gotParlist(fun.type.params, rest) &&
        t2.accept(";")
      )
    {
      namespace().add(fun);
      return true;
    } else {
      return false;
    }
  }
  void fail() {
    assert(false, "extern parsing failed at '"~t2.next_text()~"'.");
  }
  if (t2.accept("{")) {
    while (grabFun()) { }
    if (!t2.accept("}")) fail;
  } else if (!grabFun()) fail;
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotExtern, "tree.toplevel.extern_c");

Object gotImport(ref string text, ParseCb cont, ParseCb rest) {
  string m;
  // import a, b, c;
  if (!text.accept("import ")) return null;
  auto mod = namespace().get!(Module);
  if (!(
    text.bjoin(text.gotIdentifier(m, true), text.accept(","),
    { mod.imports ~= lookupMod(m); },
    true) &&
    text.accept(";")
  )) throw new Exception("Unexpected text while parsing import statement: "~text.next_text());
  return Single!(NoOp);
}
mixin DefaultParser!(gotImport, "tree.import");

Object gotModule(ref string text, ParseCb cont, ParseCb restart) {
  auto t2 = text;
  Function fn;
  Structure st;
  Tree tr;
  Module mod;
  auto backup = namespace.ptr();
  scope(exit) namespace.set(backup);
  if (t2.accept("module ") && (New(mod), namespace.set(mod), true) &&
      t2.gotIdentifier(mod.name, true) && t2.accept(";") &&
      t2.many(
        !!restart(t2, "tree.toplevel", &tr),
        { mod.entries ~= tr; }
      ) &&
      (text = t2, true)
    ) return mod;
  else return null;
}
mixin DefaultParser!(gotModule, "tree.module");
