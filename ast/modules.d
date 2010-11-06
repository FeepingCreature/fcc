module ast.modules;

import ast.base, ast.namespace, ast.structure, ast.parse;

import tools.ctfe, tools.threads;

class Module : Namespace, Tree, Named {
  string name;
  Module[] imports;
  Tree[] entries;
  Setupable[] setupable;
  AsmFile inProgress; // late to the party;
  void addSetupable(Setupable s) {
    setupable ~= s;
    if (inProgress) s.setup(inProgress);
  }
  mixin defaultIterate!(imports, entries);
  override {
    Module dup() { assert(false, "What the hell are you doing, man. "); }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      auto backup = current_module();
      current_module.set(this);
      scope(exit) current_module.set(backup);
      foreach (s; setupable) s.setup(af);
      inProgress = af;
      scope(exit) inProgress = null;
      int i; // NOTE: not a foreach! entries may yet grow.
      while (i < entries.length) {
        auto entry = entries[i++];
        entry.emitAsm(af);
      }
    }
    string mangle(string name, IType type) {
      return "module_"~this.name.replace(".", "_")~"_"~name~(type?("_of_"~type.mangle()):"");
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

Module sysmod;

extern(C) Namespace __getSysmod() { return sysmod; } // for ast.namespace

Module[string] cache;

import tools.compat: read, castLike;
Module lookupMod(string name) {
  if (name == "sys") {
    return sysmod;
  }
  if (auto p = name in cache) return *p;
  auto file = (name.replace(".", "/") ~ ".cr").read().castLike("");
  auto mod = cast(Module) parsecon.parse(file, "tree.module");
  if (!mod) throw new Exception("Could not parse module: '"~file.next_text()~"' !");
  if (file.strip().length)
    throw new Exception("Failed to parse module at '"~file.next_text()~"' !");
  cache[name] = mod;
  return mod;
}

import ast.pointer;
// not static this() to work around a precedence bug in phobos. called from fcc.
void setupSysmods() {
  string src = `
    module sys;
    alias bool = int;
    alias true = bool:1;
    alias false = bool:0;
    alias null = void*:0;
    extern(C) {
      void puts(char*);
      void printf(char*, ...);
      void* malloc(int);
      void* calloc(int, int);
      void free(void*);
      void* realloc(void* ptr, size_t size);
      void* memcpy(void* dest, src, int n);
      int memcmp(void* s1, s2, int n);
      int snprintf(char* str, int size, char* format, ...);
    }
    // before marker
    alias string = char[];
    bool strcmp(string a, b) {
      if a.length != b.length return false;
      for (int i = 0; i < a.length; ++i)
        if a[i] != b[i] return false;
      return true;
    }
    template init(T) <<EOT
      T init;
    EOT
    void* memcpy2(void* dest, src, int n) {
      // printf("memcpy(%p, %p, %i)\n", dest, src, n);
      return memcpy(dest, src, n);
    }
    context mem {
      void* delegate(int)            malloc_dg = &malloc;
      void* delegate(int, int)      calloc_dg = &calloc;
      void delegate(void*)             free_dg = &free;
      void* delegate(void*, size_t) realloc_dg = &realloc;
      void* malloc (int i)             { return malloc_dg(i); }
      void* calloc (int i, int k)      { return calloc_dg(i, k); }
      void  free   (void* p)           { free_dg(p); }
      void* realloc(void* p, size_t s) { return realloc_dg(p, s); }
      /*MARKER*/
      void append(string target, string text) {
        int newsize = target.length + text.length;
        auto newtarget = new char[newsize];
        newtarget[0 .. target.length] = target;
        newtarget[target.length .. newsize] = text;
      }
    }
    template sys_array_cast(T) <<EOT
      T sys_array_cast(void* ptr, int len, int sz1, int sz2) {
        auto destlen = len * sz1;
        if destlen % sz2 {
          writeln "Array cast failed: size/alignment mismatch. ";
          _interrupt 3;
        }
        destlen /= sz2;
        T res;
        auto resptr = typeof(res[0])*:ptr;
        res = resptr[0 .. destlen];
        return res;
      }
    EOT
    template append2(T) <<EOT
      T[~] append2(T[~]* l, T[] r) {
        // printf("append2 %i to %i, cap %i\n", r.length, l.length, l.capacity);
        if (l.capacity < l.length + r.length) {
          auto size = l.length + r.length, size2 = l.length * 2;
          auto newsize = size;
          if (size2 > newsize) newsize = size2;
          T[~] res = (new T[newsize])[0 .. size];
          res[0 .. l.length] = (*l)[];
          res[l.length .. size] = r;
          res.capacity = newsize;
          return res;
        } else {
          T[~] res = l.ptr[0 .. l.length + r.length]; // make space
          res.capacity = l.capacity;
          l.capacity = 0; // claimed!
          res[l.length .. res.length] = r;
          return res;
        }
      }
    EOT
    template append2e(T) <<EOT
      T[~] append2e(T[~]* l, T r) {
        return append2!T(l, (&r)[0..1]);
      }
    EOT
    // maybe just a lil' copypaste
    template append3(T) <<EOT
      T[auto ~] append3(T[auto ~]* l, T[] r) {
        if !r.length return *l;
        if (l.capacity < l.length + r.length) {
          auto size = l.length + r.length, size2 = l.length * 2;
          auto newsize = size;
          if (size2 > newsize) newsize = size2;
          auto full = new T[newsize];
          T[auto ~] res = T[auto~]:(full[0 .. size]);
          res.capacity = newsize;
          res[0 .. l.length] = (*l)[];
          if l.capacity // otherwise, initialized from slice
            mem.free(void*:l.ptr);
          res[l.length .. size] = r;
          return res;
        } else {
          T[auto ~] res = T[auto~]:l.ptr[0 .. l.length + r.length]; // make space
          res.capacity = l.capacity;
          l.capacity = 0; // claimed!
          res[l.length .. res.length] = r;
          return res;
        }
      }
    EOT
    template append3e(T) <<EOT
      T[auto ~] append3e(T[auto ~]* l, T r) {
        return append3!T(l, (&r)[0..1]);
      }
    EOT
    string itoa(int i) {
      if i < 0 return "-" ~ itoa(-i);
      if i == 0 return "0";
      string res;
      while i {
        char[1] temp;
        temp[0] = "0123456789"[i%10];
        res = temp ~ res;
        i = i / 10;
      }
      return res;
    }
    alias vec3f = vec(float, 3);
    string ptoa(void* p) {
      auto res = new char[size_t.sizeof * 2 + 2 + 1];
      snprintf(res.ptr, res.length, "0x%08x", p); // TODO: adapt for 64-bit
      return res[0 .. res.length - 1];
    }
    void writeln(string line) {
      printf("%.*s\n", line.length, line.ptr);
    }
    string ftoa(float f) {
      // printf("ftoa(%f)\n", f);
      // printf("ftoa(%f)\n", double:16);
      auto res = new char[20];
      double d = f;
      int len = snprintf(res.ptr, res.length, "%f", d);
      if len > res.length len = res.length;
      return res[0 .. len];
    }
    class Object {
    }
    struct GuardRecord {
      void delegate() dg;
      GuardRecord* prev;
    }
    GuardRecord* _record;
    interface IExprValue {
      IExprValue take(string type, void* target);
      bool isEmpty();
    }
    interface ITupleValue : IExprValue {
      int getLength();
      IExprValue getMember(int which);
    }
    template takeValue(T) <<EOF
      (T, IExprValue) takeValue(IExprValue iev) {
        T res = void;
        auto niev = iev.take(T.mangleof, &res);
        return (res, niev);
      }
    EOF
    import std.c.setjmp; // for conditions
    struct CondMarker {
      string name;
      void delegate(IExprValue) dg;
      CondMarker* prev;
    }
  `;
  // must generate a partial definition of sysmod first so that certain features (new) can do lookups against sys.mem correctly.
  string base = src.between("", "/*MARKER*/") ~ "}";
  sysmod = cast(Module) parsecon.parse(base, "tree.module");
  // we can now use the first half to parse the entirety.
  sysmod = cast(Module) parsecon.parse(src, "tree.module");
}

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
  Structure st;
  Tree tr;
  Module mod;
  auto backup = namespace.ptr();
  scope(exit) namespace.set(backup);
  if (t2.accept("module ")) {
    New(mod);
    namespace.set(mod);
    auto backup_mod = current_module();
    current_module.set(mod);
    scope(exit) current_module.set(backup_mod);
    if (t2.gotIdentifier(mod.name, true) && t2.accept(";") &&
      t2.many(
        !!restart(t2, "tree.toplevel", &tr),
        {
          if (auto n = cast(Named) tr)
            if (!addsSelf(tr))
              mod.add(n);
          mod.entries ~= tr;
        }
      )
    ) {
      text = t2;
      if (text.strip().length)
        throw new Exception("Unknown statement at '"~text.next_text()~"'");
      return mod;
    } else throw new Exception("Failed to parse module at '"~t2.next_text()~"'! ");
  } else return null;
}
mixin DefaultParser!(gotModule, "tree.module");
