module ast.intrinsic;

import ast.modules, ast.pointer, ast.base, ast.oop, ast.casting, ast.static_arrays;
// not static this() to work around a precedence bug in phobos. called from main.
void setupSysmods() {
  if (sysmod) return;
  string src = `
    module sys;
    pragma(lib, "m");
    alias strict bool = int;
    alias true = bool:1;
    alias false = bool:0;
    alias null = void*:0;
    alias ubyte = byte; // TODO
    alias ints = 0..-1;
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
    bool streq(char[] a, b) {
      if a.length != b.length return false;
      for (int i = 0; i < a.length; ++i)
        if a[i] != b[i] return false;
      return true;
    }
    template value-of(T) {
      alias value-of = *T*:null;
    }
    void* memcpy2(void* dest, src, int n) {
      return memcpy(dest, src, n);
    }
    context mem {
      void* delegate(int)           malloc_dg = &malloc;
      void* delegate(int, int)      calloc_dg = &calloc;
      void* delegate(int)           calloc_atomic_dg; // allocate data, ie. memory containing no pointers
      void delegate(void*)          free_dg = &free;
      void* delegate(void*, size_t) realloc_dg = &realloc;
      void* malloc (int i)             { return malloc_dg(i); }
      void* calloc_atomic (int i)      { if (!calloc_atomic_dg) return calloc(i, 1); return calloc_atomic_dg(i); }
      void* calloc (int i, int k)      { return calloc_dg(i, k); }
      void  free   (void* p)           { free_dg(p); }
      void* realloc(void* p, size_t s) { return realloc_dg(p, s); }
      /*MARKER*/
    }
    alias string = char[]; // must be post-marker for free() to work properly
    struct FrameInfo {
      string fun, pos;
      FrameInfo* prev;
    }
    FrameInfo *stackframe;
    template sys_array_cast(T) {
      template sys_array_cast(U) {
        T sys_array_cast(U u) {
          alias ar = u[0];
          alias sz1 = u[1];
          alias sz2 = u[2];
          auto destlen = ar.length * sz1;
          if destlen % sz2 {
            raise new Error "Array cast failed: size/alignment mismatch - casting $(string-of U[0]) of $(size-of U[0]) to $(string-of T) of $(size-of T) (u of $(u[(1, 2)]) for $(ar.length) => $(destlen) => $(destlen % 1)). ";
          }
          destlen /= sz2;
          T res;
          auto resptr = type-of res[0] * :ar.ptr;
          res = resptr[0 .. destlen];
          return res;
        }
      }
    }
    template append2(T) {
      T[~] append2(T[~]* l, T[] r) {
        // printf("append2 %i to %i, cap %i\n", r.length, l.length, l.capacity);
        if (l.capacity < l.length + r.length) {
          auto size = l.length + r.length, size2 = l.length * 2;
          auto newsize = size;
          if (size2 > newsize) newsize = size2;
          T[~] res = (new T[] newsize)[0 .. size];
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
    }
    template append2e(T) {
      T[~] append2e(T[~]* l, T r) {
        return append2!T(l, (&r)[0..1]);
      }
    }
    // maybe just a lil' copypaste
    template append3(T) {
      T[auto ~] append3(T[auto ~]* l, T[] r) {
        if !r.length return *l;
        if (l.capacity < l.length + r.length) {
          auto size = l.length + r.length, size2 = l.length * 2;
          auto newsize = size2;
          if (size > newsize) newsize = size;
          auto full = new T[] newsize;
          // printf("allocated %p as %d\n", full.ptr, full.length);
          T[auto ~] res = T[auto~]:(full[0 .. size]);
          res.capacity = newsize;
          res[0 .. l.length] = (*l)[];
          // printf("free %d, %p (cap %d)\n", l.length, l.ptr, l.capacity);
          if l.length && l.capacity // otherwise, initialized from slice
            mem.free(void*:l.ptr);
          // printf("done\n");
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
    }
    template append3e(T) {
      T[auto ~] append3e(T[auto ~]* l, T r) {
        // printf("hi, append3e here - incoming %d, add 1\n", l.length);
        return append3!T(l, (&r)[0..1]);
      }
    }
    string itoa(int i) {
      if i == -0x8000_0000 return "-2147483648"; // Very "special" case.
      if i < 0 return "-" ~ itoa(-i);
      if i == 0 return "0";
      string res;
      while i {
        string prefix = "0123456789"[i%10 .. i%10+1];
        res = prefix ~ res;
        i /= 10;
      }
      return res;
    }
    string btoa(bool b) {
      if b return "true";
      return "false";
    }
    string ltoa(long l) {
      auto foo = new char[] 32;
      int length = snprintf(foo.ptr, foo.length, "%lli", l);
      if (length > 0) return foo[0 .. length];
      printf ("please increase the snprintf buffer %i\n", length);
      *int*:null=0;
    }
    platform(!arm*) {
      alias vec2f = vec(float, 2);
      alias vec3f = vec(float, 3);
      alias vec4f = vec(float, 4);
      alias vec2d = vec(double, 2);
      alias vec3d = vec(double, 3);
      alias vec4d = vec(double, 4);
    }
    alias vec2i = vec(int, 2);
    alias vec3i = vec(int, 3);
    alias vec4i = vec(int, 4);
    alias vec2l = vec(long, 2);
    alias vec3l = vec(long, 3);
    alias vec4l = vec(long, 4);
    extern(C) int fgetc(void*);
    extern(C) int fflush(void*);
    platform(default) {
      extern(C) void* stdin, stdout;
    }
    string ptoa(void* p) {
      auto res = new char[]((size-of size_t) * 2 + 2 + 1);
      snprintf(res.ptr, res.length, "0x%08x", p); // TODO: adapt for 64-bit
      return res[0 .. res.length - 1];
    }
    platform(default) {
      string readln() {
        char[auto~] buffer;
        while (!buffer.length || buffer[$-1] != "\n") { buffer ~= char:byte:fgetc(stdin); }
        return buffer[0..$-1];
      }
    }
    void writeln(string line) {
      printf("%.*s\n", line.length, line.ptr);
      platform(default) { fflush(stdout); }
    }
    string dtoa(double d) {
      auto res = new char[] 128; // yes, actually does need to be this big >_>
      int len = snprintf(res.ptr, res.length, "%f", d);
      if len > res.length len = res.length;
      return res[0 .. len];
    }
    platform(!arm*) {
      string ftoa(float f) {
        short backup = fpucw;
        fpucw = short:(fpucw | 0b111_111); // mask nans
        string res = dtoa double:f;
        fpucw = backup;
        return res;
      }
    }
    /*MARKER2*/
    class Object {
      string toString() return "Object";
    }
    void* _fcc_dynamic_cast(void* ex, string id, int isIntf) {
      if (!ex) return null;
      if (isIntf) ex = void*:(void**:ex + **int**:ex);
      auto obj = Object: ex;
      // writeln "dynamic cast: obj $ex to $id => $(obj.dynamicCastTo id)";
      return obj.dynamicCastTo id;
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
    template takeValue(T) {
      (T, IExprValue) takeValue(IExprValue iev) {
        T res = void;
        auto niev = iev.take(T.mangleof, &res);
        return (res, niev);
      }
    }
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
      string param_id;
      bool accepts(Object obj) {
        if (!param_id.length) return !obj;
        else return !!obj?.dynamicCastTo param_id;
      }
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
        
        longjmp (&target, 1);
      }
    }
    
    Object handler-argument-variable;
    
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
        *int*:null = 0;
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
    class Condition {
      string msg;
      void init(string s) msg = s;
      string toString() { return "Condition: $msg"; }
    }
    // errors that change behavior in release mode
    // note: catch at your own peril!
    class UnrecoverableError : Condition {
      void init(string s) super.init "UnrecoverableError: $s";
    }
    class Error : UnrecoverableError { // haha abuse of oop
      void init(string s) super.init "Error: $s";
    }
    class Signal : Condition {
      void init(string s) { super.init "Signal: $s"; }
    }
    class BoundsError : UnrecoverableError {
      void init(string s) super.init s;
      string toString() { return "BoundsError: $(super.toString())"; }
    }
    template bounded_array_access(T) {
      alias ret = type-of (value-of!T)[0].ptr;
      ret bounded_array_access(T t) {
        auto ar = t[0];
        auto pos = t[1];
        auto info = t[2];
        if (pos >= ar.length)
          raise new BoundsError "Index access out of bounds: $pos >= length $(ar.length) at $info";
        return ar.ptr + pos;
      }
    }
    void raise(Signal sig) {
      auto cur = __hdl__;
      while cur {
        if cur.accepts(sig) cur.dg(sig);
        cur = cur.prev;
      }
    }
    void raise(UnrecoverableError err) {
      auto cur = __hdl__;
      while cur {
        if cur.accepts(err) cur.dg(err);
        cur = cur.prev;
      }
      writeln "Unhandled condition: $(err.toString()). ";
      *int*:null=0;
    }
    class MissedReturnError : UnrecoverableError {
      void init(string name) { super.init("End of $name reached without return"); }
    }
    void[] dupvcache;
    alias BLOCKSIZE = 16384;
    void missed_return(string name) {
      raise new MissedReturnError name;
    }
    void[] fastdupv(void[] v) {
      void[] res;
      if (v.length > BLOCKSIZE) {
        res = mem.malloc(v.length)[0..v.length];
      } else {
        if (dupvcache.length && dupvcache.length < v.length) {
          // can't free the middle!
          // mem.free(dupvcache.ptr);
          dupvcache = null;
        }
        if (!dupvcache.length) dupvcache = new void[] BLOCKSIZE;
        res = dupvcache[0 .. v.length];
        dupvcache = dupvcache[v.length .. $];
      }
      res[] = v;
      return res;
    }
    void* dupv(void* ptr, int length) {
      auto res = mem.malloc(length);
      memcpy(res, ptr, length);
      return res;
    }
    platform(!arm*) {
      int fastfloor(float f) {
        alias magicdelta = 0.000000015;
        alias roundeps = 0.5 - magicdelta;
        alias magic = 6755399441055744.0;
        double d = double:f - roundeps + magic;
        return (int*:&d)[0];
      }
      void fastfloor3f(vec3f v, vec3i* res) {
        (vec4f*: &v).w = 0; // prevent fp error
        if (v.x >= 1<<31 || v.y >= 1<<31 || v.z >= 1<<31) { // cvttps2dq will fail
          res.x = fastfloor(v.x);
          res.y = fastfloor(v.y);
          res.z = fastfloor(v.z);
          return;
        }
        xmm[4] = v;
        asm "cvttps2dq %xmm4, %xmm5";`"
        asm `psrld $31, %xmm4`;"`
        asm "psubd %xmm4, %xmm5";
        *res = vec3i:xmm[5];
      }
    }
    struct RefCounted {
      void delegate() onZero;
      int refs;
      void claim() { refs ++; }
      void release() { refs --; if !refs onZero(); }
    }
    reassign string replace(string source, string what, string with) {
      int i = 0;
      char[auto~] res;
      while (source.length >= what.length && i <= source.length - what.length) {
        if (source[i .. i+what.length] == what) {
          res ~= source[0 .. i]; res ~= with;
          source = source[i + what.length .. $];
          i = 0;
        } else i++;
      }
      if !res.length return source;
      res ~= source;
      return res[];
    }
    class ModuleInfo {
      string name, sourcefile;
      void* dataStart, dataEnd;
      bool compiled; // does this have an .o file?
      void init(string a, b, void* c, d, bool e) (name, sourcefile, dataStart, dataEnd, compiled) = (a, b, c, d, e);
      void function()[auto~] constructors;
      bool constructed;
      string[] _imports;
      ModuleInfo[auto~] imports;
      string toString() { return "[module $name]"; }
    }
    ModuleInfo[auto~] __modules;
    ModuleInfo lookupInfo(string name) {
      for auto mod <- __modules if mod.name == name return mod;
      raise new Error "No such module: $name";
    }
    void __setupModuleInfo() { }
    void constructModules() {
      for auto mod <- __modules {
        for auto str <- mod._imports
          mod.imports ~= lookupInfo str;
      }
      void callConstructors(ModuleInfo mod) {
        if mod.constructed return;
        mod.constructed = true;
        for auto mod2 <- mod.imports
          callConstructors mod2;
        for auto constr <- mod.constructors
          constr();
      }
      for auto mod <- __modules callConstructors mod;
    }
    extern(C) {
      int getpid();
      int readlink(char*, char* buf, int bufsz);
      int system(char*);
    }
    void print-backtrace() {
      platform(default) {
        auto pid = getpid();
        system("gdb --batch -n -ex thread -ex bt -p $pid\x00".ptr);
        // system("gdb /proc/self/exe -p \$(/proc/self/stat |awk '{print \$1}')");
      }
    }
    /* shared TODO figure out why this crashes */ string executable;
    shared int __argc;
    shared char** __argv;
    int main2(int argc, char** argv) {
      __argc = argc; __argv = argv;
      __setupModuleInfo();
      constructModules();
      
      platform(x86) {
        mxcsr |= (1 << 6) | (3 << 13) | (1 << 15); // Denormals Are Zero; Round To Zero; Flush To Zero.
      }
      executable = argv[0][0..strlen(argv[0])];
      argv ++; argc --;
      auto args = new string[] argc;
      {
        int i;
        for (auto arg <- argv[0 .. argc]) {
          args[i++] = arg[0 .. strlen(arg)];
        }
      }
      int errnum;
      set-handler (Error err) {
        writeln "Unhandled error: '$(err.toString())'. ";
        // writeln "Invoking debugger interrupt. Continue to exit. ";
        // writeln "Invoking GDB. ";
        
        print-backtrace;
        errnum = 1;
        // _interrupt 3;
        invoke-exit "main-return";
      }
      define-exit "main-return" return errnum;
    }
    int __c_main(int argc, char** argv) { // handle the callstack frame 16-byte alignment
    }
    int __win_main(void* instance, prevInstance, char* cmdline, int cmdShow) {
    }
    template Iterator(T) {
      class Iterator {
        T value;
        bool advance() { raise new Error "Iterator::advance() not implemented! "; }
      }
    }
    class AssertError : UnrecoverableError {
      void init(string s) super.init "AssertError: $s";
    }
    void assert(bool cond, string mesg = string:null) {
      if (!cond)
        if (mesg) raise new AssertError mesg;
        else raise new AssertError "Assertion failed! ";
    }
    template refs(T) {
      class refs_class {
        T t;
        int index;
        type-of-elem t* value;
        bool advance() {
          if (index == t.length) return false;
          value = &t[index++];
          return true;
        }
      }
      refs_class refs(T _t) using new refs_class { t = _t; index = 0; return that; }
    }
    (int, int) _xdiv(int a, b) {
      if (b > a) return (0, a);
      int mask = 1, res;
      int half_a = a >> 1;
      while (b <= half_a) { mask <<= 1; b <<= 1; }
      while mask {
        if (b <= a) {
          res |= mask;
          a -= b;
        }
        mask >>= 1;
        b >>= 1;
      }
      return (res, a);
    }
    int _idiv(int a, b) { return _xdiv(a, b)[0]; }
    int _mod(int a, b) { return _xdiv(a, b)[1]; }
  `.dup; // make sure we get different string on subsequent calls
  synchronized(SyncObj!(sourcefiles))
    sourcefiles["<internal:sys>"] = src;
  auto sysmodmod = fastcast!(Module) (parsecon.parse(src, "tree.module"));
  sysmodmod.splitIntoSections = true;
  sysmod = sysmodmod;
}

Module[] modlist;

import ast.fun, ast.scopes, ast.namespace,
       ast.variable, ast.vardecl, ast.literals;
void finalizeSysmod(Module mainmod) {
  auto setupfun = fastcast!(Function) (sysmod.lookup("__setupModuleInfo"));
  setupfun.parseMe();
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
    left ~= mod.getAllModuleImports();
  }
  auto modtype = fastcast!(ClassRef) (sysmod.lookup("ModuleInfo"));
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(sc);
  auto var = new Variable(modtype, null, boffs(modtype));
  sc.add(var);
  auto count = new Variable(Single!(SysInt), null, boffs(Single!(SysInt)));
  sc.add(count);
  count.initInit;
  var.initInit;
  sc.addStatement(new VarDecl(var));
  sc.addStatement(new VarDecl(count));
  
  auto backupmod = current_module();
  scope(exit) current_module.set(backupmod);
  current_module.set(fastcast!(IModule) (sysmod));
  
  modlist = list;
  
  foreach (mod; list) {
    auto mname = mod.name;
    auto fltname = mname.replace(".", "_").replace("-", "_dash_");
    Expr symdstart, symdend, compiled;
    if (mod.dontEmit) {
      symdstart = reinterpret_cast(voidp, mkInt(0));
      symdend = reinterpret_cast(voidp, mkInt(0));
      compiled = mkInt(0);
    } else {
      symdstart = new Symbol("_sys_tls_data_"~fltname~"_start");
      symdend = new Symbol("_sys_tls_data_"~fltname~"_end");
      compiled = mkInt(1);
    }
    sc.addStatement(
      iparse!(Statement, "init_modinfo", "tree.stmt")
             (`{
                 var = new ModuleInfo(name, sourcefile, symdstart, symdend, bool:compiled);
                 __modules = __modules ~ var;
               }` , "var", var, "name", mkString(mod.name),
                  "symdstart", symdstart,
                  "symdend", symdend,
                  "compiled", compiled,
                  "sourcefile", mkString(mod.sourcefile)
            )
    );
    Expr[] constrs;
    foreach (fun; mod.constrs) {
      constrs ~= new FunRefExpr(fun);
    }
    sc.addStatement(
      iparse!(Statement, "init_mod_constr", "tree.stmt")
              (`var.constructors ~= funs;
              `, sc, "var", var, "funs", new SALiteralExpr(new FunctionPointer(Single!(Void), null), constrs))
    );
    auto imps = mod.getImports();
    sc.addStatement(
      iparse!(Statement, "init_mod_import_list", "tree.stmt")
             (`var._imports = new string[] len; `,
              "var", var, "len", mkInt(imps.length))
    );
    sc.addStatement(
      iparse!(Statement, "init_mod_count_var", "tree.stmt")
             (`c = 0; `, sc, "c", count)
    );
    foreach (_mod2; imps) if (auto mod2 = fastcast!(Module) (_mod2)) {
      sc.addStatement(
        iparse!(Statement, "init_mod_imports", "tree.stmt")
               (`var._imports[c++] = mod2;`, sc,
                "var", var, "c", count, "mod2", mkString(mod2.name)));
    }
  }
  opt(setupfun);
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
      af.popStack("%eax", 4);
      af.put("cpuid");
      af.pushStack("%edx", 4);
      af.pushStack("%ecx", 4);
      af.pushStack("%ebx", 4);
      af.pushStack("%eax", 4);
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
      af.pushStack("%eax", 4);
      af.pushStack("%edx", 4);
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

class FPUCW : MValue {
  mixin defaultIterate!();
  override {
    FPUCW dup() { return this; }
    IType valueType() { return Single!(Short); }
    void emitAsm(AsmFile af) {
      af.salloc(2);
      af.put("fstcw (%esp)");
    }
  }
  void emitAssignment(AsmFile af) {
    af.put("fldcw (%esp)");
    af.sfree(2);
  }
}

Object gotFPUCW(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(FPUCW);
}
mixin DefaultParser!(gotFPUCW, "tree.expr.fpucw", "24051", "fpucw");

import ast.tuples;
class RegExpr : MValue {
  string reg;
  this(string r) { reg = r; }
  mixin defaultIterate!();
  override {
    RegExpr dup() { return this; }
    IType valueType() { return voidp; }
    void emitAsm(AsmFile af) { if (isARM && reg == "%ebp") reg = "fp"; af.pushStack(reg, nativePtrSize); }
    void emitAssignment(AsmFile af) { af.popStack(reg, nativePtrSize); }
  }
}

Object gotEBP(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(RegExpr, "%ebp");
}
mixin DefaultParser!(gotEBP, "tree.expr.ebp", "24045", "_ebp");

Object gotESI(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(RegExpr, "%esi");
}
mixin DefaultParser!(gotESI, "tree.expr.esi", "24046", "_esi");

Object gotEBX(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(RegExpr, "%ebx");
}
mixin DefaultParser!(gotEBX, "tree.expr.ebx", "24047", "_ebx");

class Assembly : LineNumberedStatementClass {
  string text;
  this(string s) { text = s; }
  mixin defaultIterate!();
  override Assembly dup() { return this; }
  override void emitAsm(AsmFile af) { super.emitAsm(af); af.put(text); }
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
  auto res = new Assembly(lit.str);
  res.configPosition(text);
  text = t2;
  return res;
}
mixin DefaultParser!(gotAsm, "tree.semicol_stmt.asm", "32", "asm");

class ConstantDefinition : Tree {
  string name;
  string[] values;
  this(string n, string[] v) { name = n; values = v; }
  void emitAsm(AsmFile af) {
    af.allocLongstant(name, values, true);
  }
  ConstantDefinition dup() { assert(false); }
  mixin defaultIterate!();
}

Object gotConstant(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("(")) t2.failparse("Opening paren required. ");
  Expr nex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &nex)
   || !gotImplicitCast(nex, (Expr ex) { return !!fastcast!(StringExpr) (foldex(ex)); }))
    t2.failparse("Expected name for constant! ");
  string name = (fastcast!(StringExpr) (foldex(nex))).str;
    
  if (!t2.accept(",")) t2.failparse("Expected comma separator. ");
  
  string[] values;
  Expr value;
  if (!t2.bjoin(
    !!rest(t2, "tree.expr", &value),
    t2.accept(","),
    {
      if (!gotImplicitCast(value, (Expr ex) { return !!fastcast!(IntExpr) (foldex(ex)); }))
        t2.failparse("Expected integer for constant value. ");
      values ~= Format((fastcast!(IntExpr) (foldex(value))).num);
    },
    false
  )) t2.failparse("Couldn't parse constant definition. ");
  if (!t2.accept(");"))
    t2.failparse("Missing ');' for constant definition. ");
  text = t2;
  return new ConstantDefinition(name, values);
}
mixin DefaultParser!(gotConstant, "tree.toplevel.constant", null, "__defConstant");

Object gotInternal(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Expected expr string for internal lookup");
  auto t = fastcast!(StringExpr) (foldex(ex));
  if (!t)
    t2.failparse("Expected static string expr for internal lookup");
  auto p = t.str in internals;
  if (!p)
    t2.failparse(Format("No '", t.str, "' found in internals[] map! "));
  if (!*p)
    t2.failparse(Format("Result for '", t.str, "' randomly null! "));
  text = t2;
  return *p;
}
mixin DefaultParser!(gotInternal, "tree.expr.internal", "24052", "__internal");

import ast.pragmas;
static this() {
  pragmas["msg"] = delegate Object(Expr ex) {
    ex = foldex(ex);
    auto se = fastcast!(StringExpr) (ex);
    if (!se) throw new Exception(Format("Expected string expression for pragma(msg), not ", ex));
    logln("# ", se.str);
    return Single!(NoOp);
  };
}
