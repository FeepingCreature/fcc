module ast.intrinsic;

import ast.modules, ast.pointer, ast.base, ast.oop;
// not static this() to work around a precedence bug in phobos. called from fcc.
void setupSysmods() {
  if (!extras) New(extras, cast(string) null);
  if (sysmod) return;
  string src = `
    module sys;
    alias bool = int;
    alias true = bool:1;
    alias false = bool:0;
    alias null = void*:0;
    alias ubyte = byte; // TODO
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
      float sqrtf(float);
      double sqrt(double);
      int strlen(char*);
    }
    bool strcmp(char[] a, b) {
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
      void append(char[] target, char[] text) {
        int newsize = target.length + text.length;
        auto newtarget = new char[newsize];
        newtarget[0 .. target.length] = target;
        newtarget[target.length .. newsize] = text;
      }
    }
    alias string = char[]; // must be post-marker for free() to work properly
    template sys_array_cast(T) <<EOT
      T sys_array_cast(void* ptr, int len, int sz1, int sz2) {
        auto destlen = len * sz1;
        if destlen % sz2 {
          writeln "Array cast failed: size/alignment mismatch. ";
          _interrupt 3;
        }
        destlen /= sz2;
        T res;
        auto resptr = type-of res[0] * :ptr;
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
      if i == -0x8000_0000 return "-2147483648"; // Very "special" case.
      if i < 0 return "-" ~ itoa(-i);
      if i == 0 return "0";
      string res;
      while i {
        char[1] prefix = ["0123456789"[i%10]];
        res = prefix ~ res;
        i /= 10;
      }
      return res;
    }
    /*string ltoa(long l) {
      if l < 0 return "-" ~ ltoa(-l);
      if l == 0 return "0";
      string res;
      while l {
        char[1] prefix = ["0123456789"[l%10]];
        res = prefix ~ res;
        l /= 10;
      }
      return res;
    }*/
    alias vec2f = vec(float, 2);
    alias vec3f = vec(float, 3);
    alias vec4f = vec(float, 4);
    alias vec2i = vec(int, 2);
    alias vec3i = vec(int, 3);
    alias vec4i = vec(int, 4);
    string ptoa(void* p) {
      auto res = new char[(size-of size_t) * 2 + 2 + 1];
      snprintf(res.ptr, res.length, "0x%08x", p); // TODO: adapt for 64-bit
      return res[0 .. res.length - 1];
    }
    void writeln(string line) {
      printf("%.*s\n", line.length, line.ptr);
    }
    string dtoa(double d) {
      auto res = new char[40];
      int len = snprintf(res.ptr, res.length, "%f", d);
      if len > res.length len = res.length;
      return res[0 .. len];
    }
    /*MARKER2*/
    class Object {
    }
    struct _GuardRecord {
      void delegate() dg;
      _GuardRecord* prev;
    }
    _GuardRecord* _record;
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
    
    struct _Handler {
      string id;
      _Handler* prev;
      void* delimit;
      void delegate(Object) dg;
      bool accepts(Object obj) {
        return eval !!obj.dynamicCastTo(id);
      }
    }

    _Handler* __hdl__;
    
    void* _cm;
    struct _CondMarker {
      string name;
      void delegate() guard_id;
      _Handler* old_hdl;
      _CondMarker* prev;
      jmp_buf target;
      void jump() {
        if (!guard_id.fun) {
          while _record { _record.dg(); _record = _record.prev; }
        } else {
          // TODO: dg comparisons
          while (_record.dg.fun != guard_id.fun) && (_record.dg.data != guard_id.data) {
            _record.dg();
            _record = _record.prev;
          }
        }
        _cm = &this;
        __hdl__ = old_hdl;
        
        longjmp (target, 1);
      }
    }
    
    _CondMarker* _lookupCM(string s, _Handler* h, bool needsResult) {
      // writeln "look up condition marker for $s";
      auto cur = _CondMarker*:_cm;
      // if (h) writeln "h is $h, elements $(h.(id, prev, delimit, dg)), cur $cur";
      while (cur && (!h || void*:cur != h.delimit)) {
        // writeln "is it $(cur.name)?";
        if (cur.name == s) return cur;
        cur = cur.prev;
      }
      if needsResult {
        writeln "No exit matched $s!";
        _interrupt 3;
      }
      // writeln "no matches";
      return _CondMarker*:null;
    }
    
    _Handler* _findHandler(Object obj) {
      auto cur = __hdl__;
      while cur {
        if cur.accepts(obj) return cur;
        cur = cur.prev;
      }
      return _Handler*:null;
      // writeln "No handler found to match $obj. ";
      // _interrupt 3;
    }

    void raise-signal(Object obj) {
      auto cur = __hdl__;
      while cur {
        if cur.accepts(obj) cur.dg(obj);
        cur = cur.prev;
      }
    }
    void raise-error(Object obj) {
      auto cur = __hdl__;
      while cur {
        if cur.accepts(obj) cur.dg(obj);
        cur = cur.prev;
      }
      writeln "Unhandled condition $obj. ";
      _interrupt 3;
    }
    template iterOnce(T) <<EOF
      class one {
        T t;
        bool done;
        T step() {
          done = true;
          return t;
        }
        bool ivalid() {
          return eval !done;
        }
      }
      one iterOnce(T t) {
        auto res = new one;
        res.t = t;
        return res;
      }
    EOF
    void[] dupvcache;
    alias BLOCKSIZE = 16384;
    void[] fastdupv(void[] v) {
      void[] res;
      if (v.length > BLOCKSIZE) {
        res = malloc(v.length)[0..v.length];
      } else {
        if (dupvcache.length && dupvcache.length < v.length) {
          // can't free the middle!
          // mem.free(dupvcache.ptr);
          dupvcache = null;
        }
        if (!dupvcache.length) dupvcache = new void[BLOCKSIZE];
        res = dupvcache[0 .. v.length];
        dupvcache = dupvcache[v.length .. $];
      }
      res[] = v;
      return res;
    }
    
    int fastfloor(float f) {
      alias magicdelta = 0.000000015;
      alias roundeps = 0.5 - magicdelta;
      alias magic = 6755399441055744.0;
      double d = f - roundeps + magic;
      return (int*:&d)[0];
    }
    void fastfloor3f(vec3f v, vec3i* res) {
      xmm[4] = v;
      asm "cvttps2dq %xmm4, %xmm5";`"
      asm `psrld $31, %xmm4`;"`
      asm "psubd %xmm4, %xmm5";
      *res = vec3i:xmm[5];
    }
    class ModuleInfo {
      string name;
      void function()[] constructors;
    }
    ModuleInfo[] __modules;
    void __setupModuleInfo() { }
    int __c_main(int argc, char** argv) {
      __setupModuleInfo();
      string[] args;
      for (auto arg <- argv[0 .. argc]) {
        args ~= arg[0 .. strlen(arg)];
      }
      int[3] align_filler = void;
    }
  `.dup; // make sure we get different string on subsequent calls
  synchronized(SyncObj!(sourcefiles))
    sourcefiles["<internal:sys>"] = src;
  sysmod = fastcast!(Module) (parsecon.parse(src, "tree.module"));
}

import ast.fun, ast.scopes, ast.namespace,
       ast.variable, ast.vardecl, ast.literals;
void finalizeSysmod(Module mainmod) {
  auto setupfun = fastcast!(Function) (sysmod.lookup("__setupModuleInfo"));
  auto sc = fastcast!(Scope) (setupfun.tree);
  Module[] list;
  Module[] left;
  bool[string] done;
  left ~= mainmod;
  while (left.length) {
    auto mod = left.take();
    if (mod.name in done) continue;
    list ~= mod;
    done[mod.name] = true;
    left ~= mod.imports;
  }
  auto modtype = fastcast!(ClassRef) (sysmod.lookup("ModuleInfo"));
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(sc);
  auto var = new Variable(modtype, null, boffs(modtype));
  var.initInit;
  auto decl = new VarDecl;
  decl.vars ~= var;
  sc.addStatement(decl);
  sc.add(var);
  foreach (mod; list) {
    sc.addStatement(
      iparse!(Statement, "init_modinfo", "tree.stmt")
             (`{var = new ModuleInfo;
               __modules ~= var;
               var.name = name;
             }` , "var", var, "name", mkString(mod.name))
    );
    foreach (fun; mod.constrs)
      sc.addStatement(
        iparse!(Statement, "init_mod_constr", "tree.stmt")
               (`var.constructors ~= fun;
               `, "var", var, "fun", fun)
      );
  }
  
}

import ast.tuples;
class CPUIDExpr : Expr {
  Expr which;
  mixin defaultIterate!(which);
  this(Expr ex) { which = ex; }
  override {
    CPUIDExpr dup() { return new CPUIDExpr(which); }
    IType valueType() { return mkTuple(Single!(SysInt), Single!(SysInt), Single!(SysInt), Single!(SysInt)); }
    void emitAsm(AsmFile af) {
      which.emitAsm(af);
      af.popStack("%eax", Single!(SysInt));
      af.put("cpuid");
      af.pushStack("%edx", Single!(SysInt));
      af.pushStack("%ecx", Single!(SysInt));
      af.pushStack("%ebx", Single!(SysInt));
      af.pushStack("%eax", Single!(SysInt));
    }
  }
}

Object gotCPUID(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Expected numeric parameter for cpuid to %eax");
  if (ex.valueType() != Single!(SysInt))
    t2.failparse("Expected number for cpuid, but got ", ex.valueType(), "!");
  text = t2;
  return new CPUIDExpr(ex);
}
mixin DefaultParser!(gotCPUID, "tree.expr.cpuid", "24044", "cpuid");

class RDTSCExpr : Expr {
  mixin defaultIterate!();
  override {
    RDTSCExpr dup() { return this; }
    IType valueType() { return mkTuple(Single!(SysInt), Single!(SysInt)); }
    void emitAsm(AsmFile af) {
      af.put("rdtsc");
      af.pushStack("%eax", Single!(SysInt));
      af.pushStack("%edx", Single!(SysInt));
    }
  }
}

Object gotRDTSC(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(RDTSCExpr);
}
mixin DefaultParser!(gotRDTSC, "tree.expr.rdtsc", "2404", "rdtsc");

class MXCSR : MValue {
  mixin defaultIterate!();
  override {
    MXCSR dup() { return this; }
    IType valueType() { return Single!(SysInt); }
    void emitAsm(AsmFile af) {
      af.salloc(4);
      af.put("stmxcsr (%esp)");
    }
  }
  void emitAssignment(AsmFile af) {
    af.put("ldmxcsr (%esp)");
    af.sfree(4);
  }
}

Object gotMXCSR(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(MXCSR);
}
mixin DefaultParser!(gotMXCSR, "tree.expr.mxcsr", "2405", "mxcsr");

import ast.tuples;
class EBPExpr : Expr {
  mixin defaultIterate!();
  override {
    EBPExpr dup() { return this; }
    IType valueType() { return voidp; }
    void emitAsm(AsmFile af) { af.pushStack("%ebp", voidp); }
  }
}

Object gotEBP(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(EBPExpr);
}
mixin DefaultParser!(gotEBP, "tree.expr.ebp", "24045", "_ebp");

class Assembly : Statement {
  string text;
  this(string s) { text = s; }
  mixin defaultIterate!();
  override Assembly dup() { return this; }
  override void emitAsm(AsmFile af) { af.put(text); }
}

import ast.literal_string, ast.fold;
Object gotAsm(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Expected string literal for asm! ");
  auto lit = fastcast!(StringExpr) (foldex(ex));
  if (!lit)
    t2.failparse("Expected string literal, not ", ex.valueType(), "!");
  text = t2;
  return new Assembly(lit.str);
}
mixin DefaultParser!(gotAsm, "tree.semicol_stmt.asm", "32", "asm");
