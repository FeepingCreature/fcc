module ast.intrinsic;

import ast.modules, ast.pointer, ast.base, ast.oop, ast.casting, ast.static_arrays, ast.parse, ast.dg, ast.arrays;
// not static this() to work around a precedence bug in phobos. called from main.
void setupSysmods() {
  if (sysmod) return;
  string src = `
    module sys;
    pragma(lib, "m");
    // can't treat int as bool, can treat bool as int
    alias strict(to) bool = int;
    alias true = bool:1;
    alias false = bool:0;
    alias null = void*:0;
    alias ints = 0..int.max;
    extern(C) {
      void puts(char*);
      int printf(char*, ...);
      int fprintf(void*, char*, ...);
      void* malloc(int);
      void* calloc(int, int);
      void free(void*);
      void* memset(void* s, int c, int n);
      void* memcpy(void* dest, src, int n);
      int memcmp(void* s1, s2, int n);
      int snprintf(char* str, int size, char* format, ...);
      float sqrtf(float);
      RenameIdentifier sqrtf C_sqrtf;
      float fabsf(float);
      RenameIdentifier fabsf C_fabsf;
      double sqrt(double);
      RenameIdentifier sqrt C_sqrt;
      int strlen(char*);
      long __divdi3(long numerator, denominator);
    }
    platform(!*-mingw*) {
      extern(C) int posix_memalign(void**, int, int);
      void* alloc16(int size) {
        void* res;
        if auto res = posix_memalign(&res, 16, size) {
          printf("malloc(%i) failed with %i\n", size, res);
          _interrupt 3;
        }
        return res;
      }
      void free16(void* ptr) { free(ptr); }
    }
    platform(*-mingw*) {
      void* alloc16(int size) {
        if (!size) return null;
        // hax!
        // if we overallocate by 16, we will always have at least
        // 4 bytes of unused space. we use this space to 
        // save the original pointer for latter retrieval
        // and passing to free.
        auto pre = malloc(size+16);
        // align to next 16-bit boundary
        auto resptr = void*: (((int:pre + 16) / 16) * 16);
        (void**:resptr)[-1] = pre;
        return resptr;
      }
      void free16(void* ptr) {
        if (!ptr) return;
        free ((void**: ptr)[-1]); // retrieve original pointer
      }
    }
    bool streq(char[] a, b) {
      if a.length != b.length return false;
      if a.ptr == b.ptr return true;
      while (a.length >= 4) {
        if ((int*:a.ptr)[0] != (int*:b.ptr)[0]) return false;
        a = a[4..$]; b = b[4..$];
      }
      if (a.length == 0) return true;
      else if (a.length == 1) return a[0] == b[0];
      else if (a.length == 2) return a[0] == b[0] && a[1] == b[1];
      else return a[0] == b[0] && a[1] == b[1] && a[2] == b[2];
      /*for (int i = 0; i < a.length; ++i)
        if a.ptr[i] != b.ptr[i] return false; // already checked length
      return true;*/
    }
    template value-of(T) {
      alias value-of = *T*:null;
    }
    extern(C) void* memcpy2(void* dest, src, int n) {
      //  printf("memcpy2(%p, %p, %i)\n", dest, src, n);
      return memcpy(dest, src, n);
    }
    context mem {
      provide "defines malloc, calloc, calloc_atomic, free, special_magic";
      void* delegate(int)           malloc_dg;
      void* delegate(int, int)      calloc_dg;
      void* delegate(int)           calloc_atomic_dg; // allocate data, ie. memory containing no pointers
      void delegate(void*, int sz = 0) free_dg;
      bool special_magic; // allocated memory is cleaned up somewhere scoped-bound
      void* malloc (int i)             { return malloc_dg(i); }
      void* calloc_atomic (int i)      { if (!calloc_atomic_dg) return calloc(i, 1); return calloc_atomic_dg(i); }
      void* calloc (int i, int k)      { return calloc_dg(i, k); }
      void  free   (void* p, int sz = 0){ free_dg(p, sz); }
      /*MARKER*/
    }
    shared (void*, int)[auto~] _allocations; // no need for tls: is only valid during startup
    void tracked_mem_init() { // like mem_init but with tracking
      mem.special_magic = true;
      mem.malloc_dg = \(int i) {
        auto res = alloc16 i;
        if i using scoped mem {
          mem_init; // switch to untracked mem for this, to prevent recursionage
          _allocations ~= (res, i);
        }
        return res;
      }
      mem.calloc_dg = \(int i, k) {
        auto res = alloc16 (i * k);
        memset(res, 0, i*k);
        if i * k using scoped mem {
          mem_init;
          _allocations ~= (res, i * k);
        }
        return res;
      }
      mem.free_dg = \(void* p, int sz = 0) {
        for ref pair <- _allocations
          if pair[0] == p pair = (null, 0);
        free16 p;
      }
      mem.calloc_atomic_dg = null;
    }
    void mem_init() {
      mem. special_magic = false;
      mem. malloc_dg = \(int i) { return alloc16 i; }
      mem. calloc_dg = \(int i, k) {
        auto res = alloc16 (i * k);
        // printf("calloc(%i, %i): %p\n", i, k, res);
        memset(res, 0, i*k);
        return res; 
      }
      mem.   free_dg = \(void* p, int sz = 0) { return free16 p; }
      mem.calloc_atomic_dg = null;
    }
    alias string = char[]; // must be post-marker for free() to work properly
    struct FrameInfo {
      string fun, pos;
      FrameInfo* prev;
    }
    FrameInfo *frameinfo;
    void __popFrameInfo(void* prev) {
      // printf("clean up %.*s\n", frameinfo.fun);
      frameinfo = prev;
    }
    pragma(internalfn, "__popFrameInfo");
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
          alias restype = type-of res[0];
          auto resptr = restype* :ar.ptr;
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
        // printf("hi, append3 here - incoming %d, add %d\n", l.length, r.length);
        if !r.length return *l;
        if (l.capacity < l.length + r.length) {
          auto size = l.length + r.length, size2 = l.length * 2;
          auto newsize = size2;
          if (size > newsize) newsize = size;
          auto full = new T[] newsize;
          // printf("allocated %p as %d\n", full.ptr, full.length);
          T[auto ~] res = full[0 .. size];
          res.capacity = newsize;
          res[0 .. l.length] = (*l)[];
          // printf("free %d, %p (cap %d)\n", l.length, l.ptr, l.capacity);
          if l.length && l.capacity // otherwise, initialized from slice
            mem.free(void*:l.ptr, l.capacity * size-of T);
          // printf("done\n");
          res[l.length .. size] = r;
          return res;
        } else {
          T[auto ~] res = l.ptr[0 .. l.length + r.length]; // make space
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
        // if (l.length > 10_000_000) { int i; i /= i; }
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
    string utoa(size_t s) {
      if s == 0 return "0";
      string res;
      while s {
        string prefix = "0123456789"[s%10 .. s%10+1];
        res = prefix ~ res;
        s /= 10;
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
      _interrupt 3;
    }
    alias vec2f = vec(float, 2);
    alias vec3f = vec(float, 3);
    alias vec4f = vec(float, 4);
    alias vec2d = vec(double, 2);
    alias vec3d = vec(double, 3);
    alias vec4d = vec(double, 4);
    alias vec2i = vec(int, 2);
    alias vec3i = vec(int, 3);
    alias vec4i = vec(int, 4);
    alias vec2l = vec(long, 2);
    alias vec3l = vec(long, 3);
    alias vec4l = vec(long, 4);
    extern(C) int fgetc(void*);
    extern(C) int fflush(void*);
    platform(!*-mingw*) {
      extern(C) void* stdin, stdout, stderr;
      extern(C) int pthread_self();
    }
    template aligned16malloc(alias Alloc) {
      void* aligned16malloc(int sz) {
        if (!sz) return null;
        // hax! (cp from mingw)
        // if we overallocate by 16, we will always have at least
        // 4 bytes of unused space. we use this space to 
        // save the original pointer for latter retrieval
        // and passing to free.
        auto pre = Alloc(sz+16);
        // align to next 16-bit boundary
        auto resptr = void*: (((int:pre + 16) / 16) * 16);
        (int*:resptr)[-1] = resptr - pre; // store delta to original pointer
        return resptr;
      }
    }
    template aligned16free(alias Free) {
      void aligned16free(void* ptr) {
        if (!ptr) return;
        Free (ptr - (int*: ptr)[-1]); // retrieve original pointer
      }
    }
    platform(*-mingw*) {
      struct __FILE {
        char* _ptr;
        int _cnt;
        char* _base;
        int _flag;
        int _file;
        int _charbuf;
        int _bufsiz;
        char* _tmpfname;
      }
      // extern(C) __FILE* _iob;
      extern(C) __FILE* _imp___iob;
      alias _iob = _imp___iob;
      alias stdin  = void*:&_iob[0];
      alias stdout = void*:&_iob[1];
      alias stderr = void*:&_iob[2];
    }
    string ptoa(void* p) {
      auto res = new char[]((size-of size_t) * 2 + 2 + 1);
      snprintf(res.ptr, res.length, "0x%08x", p); // TODO: adapt for 64-bit
      return res[0 .. res.length - 1];
    }
    string readln() {
      char[auto~] buffer;
      while (!buffer.length || buffer[$-1] != "\n") { buffer ~= char:byte:fgetc(stdin); }
      return buffer[0..$-1];
    }
    void write(string line) {
      printf("%.*s", line.length, line.ptr);
    }
    void writeln(string line) {
      printf("%.*s\n", line.length, line.ptr);
      platform(default) { fflush(stdout); }
    }
    string dtoa(double d) {
      int len = snprintf(null, 0, "%f", d);
      auto res = new char[] $ len + 1;
      snprintf(res.ptr, res.length, "%f", d);
      return res[0..$-1];
    }
    string ftoa(float f) {
      platform(!arm*) {
        // there's some sort of freak bug in llvm involving reorders past asm statements
        // despite being declared sideeffectful
        // and I just cannot be fucking arsed to track it down
        // TODO retest this maybe somewhere in 2014 when llvm got their shit together
        // short backup = fpucw;
        // fpucw = short:(fpucw | 0b111_111); // mask nans
        string res = dtoa double:f;
        // fpucw = backup;
        return res;
      }
      platform(arm*) {
        return dtoa double:f;
      }
    }
    /*MARKER2*/
    struct InterfaceData {
      string name;
      InterfaceData*[] parents;
    }
    struct ClassData {
      string name;
      int size;
      ClassData* parent;
      InterfaceData*[] iparents;
    }
    class Object {
      alias classinfo = **ClassData***: &__vtable;
      string toString() return "Object";
      void free() mem.free (void*:this, classinfo.size); // "free this". wow.
    }
    void* _fcc_dynamic_cast(void* ex, ClassData* id, int isIntf) {
      if (!ex) return null;
      // writeln "_fcc_dynamic_cast($id) obj $ex";
      // if (!isIntf) writeln "being $(Object: ex)";
      // else writeln "being intf";
      if (isIntf) ex = void*:(void**:ex + **int**:ex);
      auto obj = Object: ex;
      // writeln "dynamic cast: obj $ex to $id => $(obj.dynamicCastTo id)";
      return obj.dynamicCastTo id;
    }
    void* _fcc_dynamic_cast_to_final(void* ex, ClassData* id, int isIntf) {
      if (!ex) return null;
      if (isIntf) ex = void*:(void**:ex + **int**:ex);
      auto obj = Object: ex;
      if (obj.classinfo is id) return ex;
      return null;
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
      ClassData* id;
      _Handler* prev;
      void* delimit;
      void delegate(Object) dg;
      bool accepts(Object obj) {
        return eval !!obj.dynamicCastTo(id);
      }
    }
    
    _Handler* __hdl__;
    
    extern(C) void checkBalance(void* rec, vp, string info) {
      if (rec != vp) {
        fprintf(stderr, "Record balance mismatch: %p vs %p at %.*s", rec, vp, info);
        _interrupt 3;
      }
    }
    
    void* _cm;
    struct _CondMarker {
      string name;
      void delegate() guard_id;
      _Handler* old_hdl;
      _CondMarker* prev;
      jmp_buf target;
      ClassData* param_id;
      void* threadlocal;
      bool accepts(Object obj) {
        if (!param_id) return !obj;
        else return !!obj?.dynamicCastTo param_id;
      }
      void jump() {
        // printf("execute jump to %.*s\n", name);
        if (!guard_id.fun) {
          while _record { /*printf("unroll all: %p\n", _record);*/ _record.dg(); _record = _record.prev; }
        } else {
          // TODO: dg comparisons
          while (_record.dg.fun != guard_id.fun) || (_record.dg.data != guard_id.data) {
            // printf("invoke dg of %p\n", _record);
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
    
    interface Duplicable {
      Object dup();
    }
    _CondMarker* _lookupCM(string s, _Handler* h, bool needsResult) {
      // printf("look up condition marker for %.*s\n", s);
      auto cur = _CondMarker*:_cm;
      // if (h) printf("h is %p, elements (%.*s, %p, %p, (%p, %p)), cur %p\n", h, h.(id, prev, delimit, dg), cur);
      _CondMarker* res;
      while (cur && (!h || void*:cur != h.delimit)) {
        // printf("is it %.*s?\n", cur.name);
        if (cur.name == s) res = cur; // return the "upmost" marker that's still ahead of delimit
        cur = cur.prev;
      }
      if (res) return res;
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
      void init(string s) msg = "Error: $s";
    }
    class Signal : Condition {
      void init(string s) { super.init "Signal: $s"; }
    }
    int lastLinuxSignalRaised;
    class LinuxSignal : Error {
      int id;
      void init(string s, int id) { this.id = id; super.init "LinuxSignal: $s"; }
    }
    class MemoryAccessError : Error {
      void init(string s) { super.init "MemoryAccessError: $s"; }
    }
    class NullPointerError : MemoryAccessError {
      void init(string s) { super.init "NullPointerError: $s"; }
      void init() { init "null pointer accessed"; }
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
        if (pos >= ar.length) {
          raise new BoundsError "Index access out of bounds: $pos >= length $(ar.length) at $info";
        }
        return ar.ptr + pos;
      }
    }
    void raise(UnrecoverableError err) {
      // printf("raise2 %.*s given %p\n", err.toString(), frameinfo.prev);
      auto cur = __hdl__;
      // printf("raise here: %p %p\n", cur, &__hdl__);
      if (!cur) { int i; i /= i; }
      while cur {
        if cur.accepts(err) cur.dg(err);
        cur = cur.prev;
      }
      // printf("gdb-print-backtrace\n");
      gdb-print-backtrace();
      // printf("exit\n");
      writeln "Unhandled condition: $(err.toString()). ";
      exit 1;
    }
    pragma(noreturn, "raise");
    // This one CAN return! Put it after the pragma!
    // (remember, neat parsing order is well-defined)
    void raise(Signal sig) {
      // printf("Raise1 %.*s\n", sig.toString());
      auto cur = __hdl__;
      while cur {
        if cur.accepts(sig) cur.dg(sig);
        cur = cur.prev;
      }
    }
    class MissedReturnError : UnrecoverableError {
      void init(string name) { super.init("End of $name reached without return"); }
    }
    void missed_return(string name) {
      raise new MissedReturnError name;
    }
    void[] dupvcache, initial_dupvcache; int referents;
    alias BLOCKSIZE = 16384;
    // range, references
    (void[], int)[auto~] dupv_archive;
    void dupvfree(void* p) {
      p = (void**:p)[-1];
      for (int i = dupv_archive.length - 1; i >= 0; --i) {
        ref entry = dupv_archive[i];
        if (!entry[1]) continue;
        if (entry[0].(int:ptr <= int:p < int:ptr+length)) entry[1] --;
        if (!entry[1]) { // cleanup
          // entry[0].free; // doesn't work yet in intrinsic
          mem.free entry[0].ptr;
        }
      }
    }
    void[] fastdupv(void[] v) {
      assert ((int:v.ptr)&0b11 == 0); // must be 4-aligned
      void[] res;
      // use the same hack as alloc16 - overalloc by 16 so we can match the
      // alignment of v and keep a pointer to the original around in the start
      int toalloc = v.length + 16;
      // if special_magic is true, can't rely on memory to stick around so can't use cache
      if (v.length > BLOCKSIZE || mem.special_magic) {
        res = mem.malloc(toalloc)[0..toalloc];
      } else {
        if (dupvcache.length < toalloc) {
          dupvcache = null;
        }
        if (!dupvcache.length) {
          if (initial_dupvcache)
            dupv_archive ~= (initial_dupvcache, referents);
          referents = 0;
          dupvcache = new void[] BLOCKSIZE;
          initial_dupvcache = dupvcache;
        }
        res = dupvcache[0 .. toalloc];
        dupvcache = dupvcache[toalloc .. $];
        referents ++;
      }
      // alloc res to v
      auto original_res = res;
      do res = res[4..$];
      while (int:res.ptr & 0b1111 != int:v.ptr & 0b1111);
      (void**:res.ptr)[-1] = original_res.ptr; // store original pointer
      res[0..v.length] = v;
      return res[0..v.length];
    }
    void* dupv(void* ptr, int length) {
      auto res = mem.malloc(length);
      memcpy(res, ptr, length);
      return res;
    }
    int fastfloor(float f) { return (int:f) - (*int*:&f) >>> 31; }
    void fastfloor3f(vec3f v, vec3i* res) {
      if (v.x > int.max || v.y > int.max || v.z > int.max) {
        fail("fastfloor3f int conversion requested but there is actually no int equivalent for $v");
      }
      (vec4f*: &v).w = 0; // prevent fp error
      vec4i i = vec4i: *(vec4f*:&v); // cvttps2dq
      vec4i signs = *(vec4i*: &v) >>> 31; // logical shift sign bit into bit0
      // sign=1 means negative, so subtract that 1 to make -6.5 <> -6 <> -7
      *(vec4i*: res) = (i - signs);
      // should be same assembly
      /*
      xmm[4] = v;
      asm "cvttps2dq %xmm4, %xmm5";`"
      asm `psrld $31, %xmm4`;"`
      asm "psubd %xmm4, %xmm5";
      *res = vec3i:xmm[5];*/
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
    struct FunctionInfo {
      string name;
      void* ip-from, ip-to;
      int* linenr_sym;
      string toString() { return "($name[$ip-from..$ip-to] $(*linenr_sym) line entries)"; }
    }
    class ModuleInfo {
      string name, sourcefile;
      void* dataStart, dataEnd;
      bool compiled; // does this have an .o file?
      void init(string a, b, void* c, d, bool e, void function()[] co, string[] i, FunctionInfo[] f, ClassData*[] cl) {
        (name, sourcefile, dataStart, dataEnd, compiled) = (a, b, c, d, e);
        // (base*: dupv (ptr, length * size-of base))[0 .. length]
        // no .dup yet for some reason
        constructors = (void function()*: dupv(co.(ptr, length * size-of type-of *ptr)))[0 .. co.length];
        _imports = (string*: dupv(i.(ptr, length * size-of string)))[0 .. i.length];
        functions = (FunctionInfo*: dupv(f.(ptr, length * size-of FunctionInfo)))[0 .. f.length];
        classes = (ClassData**: dupv(cl.(ptr, length * size-of ClassData*)))[0 .. cl.length];
      }
      void function()[] constructors;
      bool constructed;
      string[] _imports;
      FunctionInfo[] functions;
      ModuleInfo[auto~] imports;
      ClassData*[] classes;
      string toString() {
        if !functions return "[module $name imports $([for m <- imports: m.name].eval[])]";
        return "[module $name imports $([for m <- imports: m.name].eval[]) ($functions)]";
      }
    }
    
    shared ModuleInfo[auto~] __modules;
    
    extern(C) int __module_map_length;
    extern(C) void* __module_map;
    alias __static_modules = [for i <- 0..__module_map_length: (void* dataStart, void* dataEnd): ((void**:&__module_map)[i*2], (void**:&__module_map)[i*2+1])];
    
    ModuleInfo lookupInfo(string name) {
      for auto mod <- __modules if mod.name == name return mod;
      raise new Error "No such module: $name";
    }
    extern(C) void __setupModuleInfo(void* _threadlocal);
    void constructModules() {
      for auto mod <- __modules.iterator {
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
      for auto mod <- __modules {
        callConstructors mod;
      }
    }
    shared Error preallocated_sigsegv, preallocated_nullfault;
    bool already_handling_segfault;
    void _check_handling() {
      if (already_handling_segfault) {
        writeln "A segfault has occurred while handling a previous segfault. Error handling is compromised; program will exit. ";
        exit(1);
      }
    }
    alias _null_dead_zone = 4096;
    platform(default) {
      pragma(lib, "pthread");
      static import c.pthread, c.signal;
      void setup-segfault-handler() {
        c.signal._sigaction sa;
        sa.flags = c.signal.SA_SIGINFO;
        sigemptyset (&sa.mask);
        sa.sigaction = &sighandle;
        if (sigaction(c.signal.SIGSEGV, &sa, null) == -1)
          raise new Error "failed to setup SIGSEGV handler";
        if (sigaction(c.signal.SIGINT, &sa, null) == -1)
          raise new Error "failed to setup SIGINT handler";
        // if (sigaction(c.signal.SIGFPE, &sa, null) == -1)
        //   raise new Error "failed to setup SIGFPE handler";
      }
      extern(C) void* getThreadlocal() {
        return c.pthread.pthread_getspecific(tls_pointer);
      }
      void setThreadlocal(void* p) {
        c.pthread.pthread_setspecific(tls_pointer, p);
      }
      void* errptr;
      extern(C) {
        enum X86Registers {
          GS, FS, ES, DS, EDI, ESI, EBP, ESP, EBX, EDX, ECX, EAX, TRAPNO, ERR, EIP, CS, EFL, UESP, SS
        }
        struct mcontext_t {
          int x 19 gregs;
          void* fpregs;
          size_t oldmask;
          size_t cr2;
        }
        struct siginfo_t {
          int si_signo, si_errno, si_code;
          void* si_addr;
          // some more stuff
        }
        struct ucontext {
          size_t flags;
          ucontext* link;
          c.signal.stack_t stack;
          c.signal.mcontext_t mcontext;
          __sigset_t sigmask;
        }
        void seghandle_userspace() {
          auto _threadlocal = getThreadlocal;
          _check_handling;
          already_handling_segfault = true;
          onExit already_handling_segfault = false;
          bool isnullp = 0 <= int:errptr < _null_dead_zone;
          if (preallocated_sigsegv) {
            if (isnullp) raise preallocated_nullfault;
            raise preallocated_sigsegv;
          }
          if (isnullp)
            raise new NullPointerError;
          raise new MemoryAccessError "Segmentation Fault";
        }
        void sighandle_userspace() {
          auto _threadlocal = getThreadlocal;
          raise new LinuxSignal ("Signal $(lastLinuxSignalRaised)", lastLinuxSignalRaised);
        }
        void sighandle(int sig, siginfo_t* si, void* unused) {
          auto uc = ucontext*: unused;
          ref gregs = uc.mcontext.gregs;
          ref
            eip = void*:gregs[X86Registers.EIP],
            esp = void**:gregs[X86Registers.ESP];
          // imitate the effects of "call seghandle_userspace"
          esp --;
          *esp = eip;
          auto _threadlocal = getThreadlocal;
          // return like call
          if (sig == c.signal.SIGSEGV) {
            errptr = si.si_addr;
            eip = void*: &seghandle_userspace;
          } else {
            lastLinuxSignalRaised = sig;
            eip = void*: &sighandle_userspace;
          }
        }
        struct __sigset_t {
          byte x 128 __val;
        }
        struct _sigaction {
          void function(int, siginfo_t*, void*) sigaction;
          __sigset_t mask;
          int flags;
          void function() restorer;
        }
        int pthread_key_create(c.pthread.pthread_key_t*, void function(void*));
        int sigemptyset(__sigset_t* set);
        int sigaction(int sig, _sigaction* act, _sigaction* oact);
      }
      shared c.pthread.pthread_key_t tls_pointer;
    }
    platform(*-mingw32*) {
      pragma(include_prepend, "winbase.h < excpt.h");
      import c.windows, c.excpt;
      alias DWORD = int;
      shared DWORD tls_pointer;
      alias PEXCEPTION_HANDLER = EXCEPTION_DISPOSITION function(_EXCEPTION_RECORD*, _EXCEPTION_REGISTRATION*, _CONTEXT*, _EXCEPTION_RECORD*);
      shared _EXCEPTION_REGISTRATION reg;
      int errcode;
      void* errptr;
      extern(C) void* getThreadlocal() {
        return TlsGetValue(tls_pointer);
      }
      void setThreadlocal(void* p) {
        TlsSetValue(tls_pointer, p);
      }
      extern(C) void seghandle_userspace() {
        auto _threadlocal = getThreadlocal;
        _check_handling;
        already_handling_segfault = true;
        onExit already_handling_segfault = false;
        
        if (errcode == int:STATUS_ACCESS_VIOLATION) {
          // printf("seghandle_userspace and %p\n", frameinfo);
          bool isnullp = 0 <= int:errptr < _null_dead_zone;
          if (preallocated_sigsegv) {
            if (isnullp) raise preallocated_nullfault;
            raise preallocated_sigsegv;
          }
          if (isnullp)
            raise new NullPointerError;
          raise new MemoryAccessError "Access Violation";
        }
        raise new Error "Windows SEH Code $(void*:errcode)";
      }
      extern(C) EXCEPTION_DISPOSITION seghandle(_EXCEPTION_RECORD* record, void* establisher_frame, _CONTEXT* context, void* dispatcher_context) {
        // printf("seghandle(%p (%p), %p, %p, %p)\n", record, record.ExceptionCode, establisher_frame, context, dispatcher_context);
        auto _threadlocal = TlsGetValue(tls_pointer);
        errcode = record.ExceptionCode;
        errptr = void*: record.ExceptionInformation[1];
        ref
          esp = void**:context.Esp,
          eip = void* :context.Eip;
        // imitate the effects of "call seghandle_userspace"
        // stack grows down under windows
        esp --;
        *esp = eip;
        eip = void*: &seghandle_userspace; // rewrite for return-to-lib
        return ExceptionContinueExecution; // and jump!
        // return ExceptionContinueSearch;
      }
    }
    extern(C) {
      int getpid();
      int readlink(char*, char* buf, int bufsz);
      int system(char*);
      void exit(int);
    }
    RenameIdentifier system C_system; // prevent collision with std.process
    void gdb-print-backtrace() {
      platform(default) {
        auto pid = getpid();
        alias text = "gdb --batch -n -ex thread -ex bt -p %i";
        auto size = snprintf(null, 0, text, pid);
        auto ptr = malloc(size+1);
        snprintf(ptr, size+1, text, pid);
        C_system(ptr);
        // C_system("gdb --batch -n -ex thread -ex bt -p $pid\x00".ptr);
        // C_system("gdb /proc/self/exe -p \$(/proc/self/stat |awk '{print \$1}')");
      }
    }
    shared string executable;
    shared int __argc;
    shared char** __argv;
    extern(C) byte _sys_tls_data_start;
    
    shared int tls_size;
    
    extern(C) (int, int) setupTLSSize() {
      int dataStart = 0x7fff_ffff, dataEnd;
      
      auto
        localStart = [for mod <- __static_modules: int:mod.dataStart - int:&_sys_tls_data_start],
        localEnd = [for mod <- __static_modules: int:mod.dataEnd - int:&_sys_tls_data_start],
        localRange = zip(localStart, localEnd);
      for (auto tup <- zip(__static_modules, localRange)) {
        alias mod = tup[0], range = tup[1];
        if (range[0] < dataStart) dataStart = range[0];
        if (range[1] > dataEnd)   dataEnd   = range[1];
      }
      alias dataSize = dataEnd - dataStart; tls_size = dataSize;
      return (dataStart, dataEnd);
    }
    void add_tls_tracking() {
      // copypaste from below
      auto
        localStart = [for mod <- __static_modules: int:mod.dataStart - int:&_sys_tls_data_start],
        localEnd = [for mod <- __static_modules: int:mod.dataEnd - int:&_sys_tls_data_start],
        localRange = zip(localStart, localEnd);
      using scoped mem {
        mem_init();
        for auto range <- localRange {
          _allocations ~= (_threadlocal + range[0], range[1] - range[0]);
        }
      }
    }
    extern(C) void* copy_tls() {
      (int dataStart, int dataEnd) = setupTLSSize();
      alias dataSize = dataEnd - dataStart;
      void* sourceptr = void*: &_sys_tls_data_start;
      auto oldArea = sourceptr[dataStart..dataEnd];
      auto newArea = (malloc(dataSize+16) - dataStart)[0 .. dataEnd];
      // align new area to preserve 16-byte alignment of old area
      alias matches = int:newArea.ptr&0xf == int:sourceptr&0xf;
      for 0..16 {
        if (matches) break;
        newArea.ptr ++;
      }
      if (!matches) { fprintf(stderr, "feep fails at math because he thought this was impossible\n"); int i; i /= i; }
      
      auto
        localStart = [for mod <- __static_modules: int:mod.dataStart - int:&_sys_tls_data_start],
        localEnd = [for mod <- __static_modules: int:mod.dataEnd - int:&_sys_tls_data_start],
        localRange = zip(localStart, localEnd);
      
      for (auto range <- localRange) {
        newArea[range[0] .. range[1]] = sourceptr[range[0] .. range[1]];
      }
      return newArea.ptr;
    }
    int main2(int argc, char** argv) {
      __argc = argc; __argv = argv;
      
      tracked_mem_init();
      add_tls_tracking();
      platform(default) {
        pthread_key_create(&tls_pointer, null);
        setThreadlocal _threadlocal;
        setup-segfault-handler();
        preallocated_sigsegv = new MemoryAccessError "Segmentation Fault";
        preallocated_nullfault = new NullPointerError;
      }
      platform(*-mingw32*) {
        tls_pointer = TlsAlloc();
        if (tls_pointer == TLS_OUT_OF_INDEXES)
          fail "TlsAlloc failed";
        setThreadlocal _threadlocal;
        _EXCEPTION_REGISTRATION reg;
        reg.prev = _fs0;
        reg.handler = type-of reg.handler: &seghandle;
        _fs0 = &reg;
        onExit {
          _fs0 = reg.prev;
        }
        preallocated_sigsegv = new MemoryAccessError "Access Violation";
        preallocated_nullfault = new NullPointerError;
      }
      
      int errnum;
      set-handler (UnrecoverableError err) {
        gdb-print-backtrace;
        if (!!mem.calloc_dg) writeln "Unhandled error: '$(err.toString())'. ";
        else writeln "Unhandled error: memory context compromised"; // huh.
        
        // platform(*-mingw32) { _interrupt 3; }
        errnum = 1;
        // _interrupt 3;
        invoke-exit "main-return";
      }
      define-exit "main-return" return errnum;
      
      __setupModuleInfo(_threadlocal);
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
      mem_init();
    }
    extern(C) int mcheck(int);
    extern(C) int __c_main(int argc, char** argv) { // handle the callstack frame 16-byte alignment
      // mcheck(0);
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
      static if (__release_mode) { }
      else {
        if (!cond)
          if (mesg) raise new AssertError mesg;
          else raise new AssertError "Assertion failed! ";
      }
    }
    class FailError : UnrecoverableError {
      void init() super.init "Something went wrong. ";
      void init(string s) super.init "Something went wrong: $s. ";
    }
    void fail() {
      raise new FailError;
    }
    void fail(string s) {
      raise new FailError s;
    }
    pragma(noreturn, "fail");
    template refs(T) {
      struct refs_iterator {
        T t;
        int index;
        type-of-elem t* value;
        bool advance() {
          if (index == t.length) return false;
          value = &t[index++];
          return true;
        }
      }
      refs_iterator refs(T _t) { refs_iterator res; res.t = _t; res.index = 0; return res; }
    }
    template irefs(T) {
      struct irefs_iterator {
        type-of (*T*:null).iterator t;
        int index;
        type-of-elem t * value;
        bool advance() {
          if (!auto ignore <- t) return false;
          value = &t.value;
          return true;
        }
      }
      irefs_iterator irefs(T _t) { irefs_iterator res; res.t = _t.iterator; res.index = 0; return res; }
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
    template toDg(T) {
      auto toDg(T t) {
        alias args = ParamTypes T;
        return __internal_flatten new λ(ParamTypes T args) -> t args;
      }
    }
    template New(T) {
      void New(T t) {
        static if (type-is tuple T) {
          alias obj = *(t[0]);
          alias classtype = type-of obj;
          static if (!type-is class classtype) { pragma(fail, ((string-of classtype)~" is not a class: cannot New()")); }
          obj = new classtype t[1..$];
        } else {
          alias obj = *t;
          alias classtype = type-of obj;
          static if (!type-is class classtype) { pragma(fail, ((string-of classtype)~" is not a class: cannot New()")); }
          obj = new classtype;
        }
      }
    }
  `.dup; // make sure we get different string on subsequent calls
  synchronized(SyncObj!(sourcefiles))
    sourcefiles["sys.nt"] = src;
  auto sysmodmod = fastcast!(Module) (parse(src, "tree.module"));
  if (isWindoze())
    sysmodmod._add("_fs0", fastalloc!(FS0)());
  
  if (releaseMode)
    sysmodmod._add("__release_mode", sysmod.lookup("true"));
  else
    sysmodmod._add("__release_mode", sysmod.lookup("false"));
  
  sysmodmod.splitIntoSections = true;
  sysmod = sysmodmod;
}

Module[] modlist;

import ast.fun, ast.scopes, ast.namespace,
       ast.variable, ast.vardecl, ast.literals;
void finalizeSysmod(Module mainmod) {
  auto backupmod = current_module();
  scope(exit) current_module.set(backupmod);
  current_module.set(fastcast!(IModule)(mainmod));
  
  // auto setupfun = fastcast!(Function) (sysmod.lookup("__setupModuleInfo"));
  auto setupfun = new Function;
  with (setupfun) {
    name = "__setupModuleInfo";
    extern_c = true;
    type = new FunctionType;
    type.ret = Single!(Void);
    type.params ~= Argument(voidp, "_threadlocal");
    sup = mainmod;
    coarseSrc = "{}".dup;
    coarseModule = mainmod;
    fixup();
    parseMe();
  }
  mainmod.addEntry(setupfun);
  auto sc = fastcast!(Scope) (setupfun.tree);
  Module[] list;
  list ~= mainmod;
  bool[string] checked;
  int i;
  while (i < list.length) {
    auto mod = list[i++];
    foreach (mod2; mod.getAllModuleImports()) {
      if (!(mod2.name in checked)) {
        list ~= mod2;
        checked[mod2.name] = true;
      }
    }
  }
  auto modtype = fastcast!(ClassRef) (sysmod.lookup("ModuleInfo"));
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(sc);
  auto var = fastalloc!(Variable)(modtype, framelength(), cast(string) null);
  sc.add(var);
  auto vs = fastalloc!(VarDecl)(var);
  vs.initInit;
  sc.addStatement(vs);
  
  current_module.set(fastcast!(IModule) (mainmod));
  
  modlist = list;
  
  sc.addStatement(fastalloc!(ExprStatement)(fastalloc!(CallbackExpr)("gen module info", Single!(Void), cast(Expr) null,
  list /apply/ (Module[] list, Expr bogus, LLVMFile lf) {
    string[] strlist;
    foreach (mod; list) if (!mod.dontEmit) {
      auto fltname = mod.name.replace(".", "_").replace("-", "_dash_");
      auto name = qformat("_sys_tls_data_", fltname);
      auto start = qformat(name, "_start");
      auto end = qformat(name, "_end");
      strlist ~= qformat("i8* @", start, ", i8* @", end);
    }
    putSection(lf, "module", "@__module_map = constant [", strlist.length * 2, " x i8*] ", strlist);
    putSection(lf, "module", "@__module_map_length = constant i32 ", strlist.length);
    push(lf, "undef");
  })));
  
  Expr[] tuples;
  foreach (mod; list) {
    auto mname = mod.name;
    auto fltname = mname.replace(".", "_").replace("-", "_dash_");
    Expr symdstart, symdend, compiled;
    if (mod.dontEmit) {
      symdstart = reinterpret_cast(voidp, mkInt(0));
      symdend = reinterpret_cast(voidp, mkInt(0));
      compiled = mkInt(0);
    } else {
      symdstart = fastalloc!(Symbol)(qformat("_sys_tls_data_", fltname, "_start"), Single!(Void));
      symdend = fastalloc!(Symbol)(qformat("_sys_tls_data_", fltname, "_end"), Single!(Void));
      compiled = mkInt(1);
    }
    
    Expr[] constrs;
    foreach (fun; mod.constrs) {
      constrs ~= fastalloc!(FunRefExpr)(fun);
    }
    
    Expr[] impstrings;
    auto imps = mod.getAllModuleImports();
    foreach (_mod2; imps) if (auto mod2 = fastcast!(Module) (_mod2))
      impstrings ~= mkString(mod2.name);
    
    Expr[] classptrs;
    auto classdata = fastcast!(IType)(sysmod.lookup("ClassData"));
    
    foreach (entry; mod.entries) {
      Class cl;
      if (auto cr = fastcast!(ClassRef) (entry)) cl = cr.myClass;
      else if (auto entry_cl = fastcast!(Class) (entry)) cl = entry_cl;
      if (cl) {
        classptrs ~= reinterpret_cast(fastalloc!(Pointer)(classdata), fastalloc!(Symbol)(cl.cd_name(), Single!(Void)));
      }
    }
    
    Expr[] constrexprs;
    constrexprs ~= mkString(mod.name);
    constrexprs ~= mkString(mod.sourcefile);
    constrexprs ~= symdstart;
    constrexprs ~= symdend;
    constrexprs ~= reinterpret_cast(fastcast!(IType)(sysmod.lookup("bool")), compiled);
    constrexprs ~= staticToArray(mkSALit(fastalloc!(FunctionPointer)(Single!(Void), cast(Argument[]) null), constrs));
    constrexprs ~= staticToArray(mkSALit(Single!(Array, Single!(Char)), impstrings));
    Expr nulf = fastcast!(Expr)(sysmod.lookup("null"));
    IType cmp = fastalloc!(Array)(fastcast!(IType)(sysmod.lookup("FunctionInfo")));
    if (!gotImplicitCast(nulf, cmp, (IType it) { return test(it == cmp); })) fail;
    constrexprs ~= nulf;
    constrexprs ~= staticToArray(mkSALit(fastalloc!(Pointer)(classdata), classptrs));
    tuples ~= mkTupleExpr(constrexprs);
    // version(CustomDebugInfo) {
    static if (false) { // TODO fix
      foreach (entry; mod.entries) if (auto fun = fastcast!(Function) (entry)) if (!fun.extern_c) {
        sc.addStatement(
          iparse!(Statement, "init_fun_list", "tree.stmt")
                (`var.functions ~= FunctionInfo:(name, from, to, linenr);`, sc,
                  "var", var,
                  "from", new Symbol(fun.fun_start_sym()), "to", new Symbol(fun.fun_end_sym()),
                  "name", mkString(fun.name), "linenr", new Symbol(fun.fun_linenr_sym())));
      }
    }
  }
  auto sa = mkSALit(tuples[0].valueType(), tuples);
  sc.addStatement(
    iparse!(Statement, "init_modinfo", "tree.stmt")
           (`{ for auto tup <- sa
               __modules ~= new ModuleInfo tup;
             }`,sc,
               "sa", staticToArray(sa)
           )
  );
  // too slow
  // opt(setupfun);
}

import ast.tuples;
class CPUIDExpr : Expr {
  Expr which;
  mixin defaultIterate!(which);
  mixin defaultCollapse!();
  this(Expr ex) { which = ex; }
  override {
    CPUIDExpr dup() { return fastalloc!(CPUIDExpr)(which); }
    IType valueType() { return mkTuple(Single!(SysInt), Single!(SysInt), Single!(SysInt), Single!(SysInt)); }
    void emitLLVM(LLVMFile lf) {
      todo("CPUIDExpr::emitLLVM");
      /*which.emitLLVM(lf);
      lf.popStack("%eax", 4);
      lf.put("cpuid");
      lf.pushStack("%edx", 4);
      lf.pushStack("%ecx", 4);
      lf.pushStack("%ebx", 4);
      lf.pushStack("%eax", 4);*/
    }
  }
}

Object gotCPUID(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.bin", &ex))
    t2.failparse("Expected numeric parameter for cpuid to %eax");
  if (ex.valueType() != Single!(SysInt))
    t2.failparse("Expected number for cpuid, but got ", ex.valueType(), "!");
  text = t2;
  return fastalloc!(CPUIDExpr)(ex);
}
mixin DefaultParser!(gotCPUID, "tree.expr.cpuid", "24044", "cpuid");

class RDTSCExpr : Expr {
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    RDTSCExpr dup() { return this; }
    IType valueType() { return Single!(Long); }
    void emitLLVM(LLVMFile lf) {
      auto f = save(lf, "alloca i64, i32 1");
      put(lf, `call void asm sideeffect "rdtsc; movl %eax, ($0); movl %edx, 4($0)", "r"(i64* `, f, `)`);
      load(lf, "load i64* ", f);
    }
  }
}

Object gotRDTSC(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(RDTSCExpr);
}
mixin DefaultParser!(gotRDTSC, "tree.expr.rdtsc", "2404", "rdtsc");

class MXCSR : MValue {
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    MXCSR dup() { return this; }
    IType valueType() { return Single!(SysInt); }
    void emitLLVM(LLVMFile lf) {
      load(lf, `call i32 asm sideeffect "subl $$4, %esp; stmxcsr (%esp); popl $0", "=r"()`);
    }
  }
  void emitAssignment(LLVMFile lf) {
    put(lf, `call void asm sideeffect "pushl $0; ldmxcsr (%esp); addl $$4, %esp", "r"(i32 `, lf.pop, `)`);
  }
}

Object gotMXCSR(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(MXCSR);
}
mixin DefaultParser!(gotMXCSR, "tree.expr.mxcsr", "2405", "mxcsr");

class FPUCW : MValue {
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    FPUCW dup() { return this; }
    IType valueType() { return Single!(Short); }
    void emitLLVM(LLVMFile lf) {
      load(lf, `call i16 asm "subl $$2, %esp; fstcw (%esp); popw $0", "=r"()`);
    }
  }
  void emitAssignment(LLVMFile lf) {
    put(lf, `call void asm "pushw $0; fldcw (%esp); addl $$2, %esp", "r"(i16 `, lf.pop, `)`);
  }
}

Object gotFPUCW(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(FPUCW);
}
mixin DefaultParser!(gotFPUCW, "tree.expr.fpucw", "24051", "fpucw");

// FS:0 for SEH under Windows
class FS0 : MValue {
  mixin defaultIterate!();
  mixin defaultCollapse!();
  const fs0expr = "i8* addrspace(257)* inttoptr(i32 0 to i8* addrspace(257)*)";
  this() { }
  override {
    string toString() { return "FS:0"; }
    FS0 dup() { return this; }
    IType valueType() { return voidp; }
    void emitLLVM(LLVMFile lf) {
      load(lf, "load ", fs0expr);
    }
    void emitAssignment(LLVMFile lf) {
      put(lf, "store ", typeToLLVM(valueType()), " ", lf.pop(), ", ", fs0expr);
    }
  }
}

import ast.tuples;
class RegExpr : MValue {
  string reg;
  this(string r) { reg = r; }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  override {
    string toString() { return qformat("<reg ", reg, ">"); }
    RegExpr dup() { return this; }
    IType valueType() { return voidp; }
    void emitLLVM(LLVMFile lf) {
      if (reg == "%ebp") {
        lf.push("%__stackframe");
        return;
      }
      todo(qformat("RegExpr(", reg, ")::emitLLVM"));
      // if (isARM && reg == "%ebp") reg = "fp"; lf.pushStack(reg, nativePtrSize);
    }
    void emitAssignment(LLVMFile lf) {
      logln("RegExpr::emitAssignment to ", reg);
      fail;
      // lf.popStack(reg, nativePtrSize);
    }
  }
}

Object gotEBP(ref string text, ParseCb cont, ParseCb rest) {
  return Single!(RegExpr, "%ebp");
}
mixin DefaultParser!(gotEBP, "tree.expr.ebp", "24045", "_ebp");

Object gotESI(ref string text, ParseCb cont, ParseCb rest) {
  text.failparse("no longer relevant in llvm, use _threadlocal instead");
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
  mixin defaultCollapse!();
  override Assembly dup() { return this; }
  override void emitLLVM(LLVMFile lf) {
    super.emitLLVM(lf);
    // todo("Assembly::emitLLVM .. :sigh:");
    put(lf, "call void asm sideeffect \"", text.replace("$", "$$"), "\", \"\"()");
  }
}

import ast.literal_string, ast.fold;
Object gotAsm(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (!rest(t2, "tree.expr _tree.expr.bin", &ex))
    t2.failparse("Expected string literal for asm! ");
  opt(ex);
  auto lit = fastcast!(StringExpr) (ex);
  if (!lit)
    t2.failparse("Expected string literal, not ", ex.valueType(), "!");
  auto res = fastalloc!(Assembly)(lit.str);
  res.configPosition(text);
  text = t2;
  return res;
}
mixin DefaultParser!(gotAsm, "tree.semicol_stmt.asm", "25", "asm");

class ConstantDefinition : Tree {
  string name;
  string[] values;
  this(string n, string[] v) { name = n; values = v; }
  void emitLLVM(LLVMFile lf) {
    preserve ~= ","~name;
    allocLongstant(lf, name, values, false);
  }
  ConstantDefinition dup() { assert(false); }
  mixin defaultIterate!();
  mixin defaultCollapse!();
}

Object gotConstant(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("(")) t2.failparse("Opening paren required. ");
  Expr nex;
  if (!rest(t2, "tree.expr _tree.expr.bin", &nex)
   || !gotImplicitCast(nex, (Expr ex) { opt(ex); return !!fastcast!(StringExpr) (ex); }))
    t2.failparse("Expected name for constant! ");
  opt(nex);
  string name = (fastcast!(StringExpr) (nex)).str;
    
  if (!t2.accept(",")) t2.failparse("Expected comma separator. ");
  
  string[] values;
  Expr value;
  if (!t2.bjoin(
    !!rest(t2, "tree.expr", &value),
    t2.accept(","),
    {
      if (!gotImplicitCast(value, (Expr ex) { opt(ex); return !!fastcast!(IntExpr) (ex); }))
        t2.failparse("Expected integer for constant value. ");
      opt(value);
      values ~= Format((fastcast!(IntExpr) (value)).num);
    },
    false
  )) t2.failparse("Couldn't parse constant definition. ");
  if (!t2.accept(");"))
    t2.failparse("Missing ');' for constant definition. ");
  text = t2;
  return fastalloc!(ConstantDefinition)(name, values);
}
mixin DefaultParser!(gotConstant, "tree.toplevel.constant", null, "__defConstant");

Object gotTerriblePapplyHack(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(text, "tree.expr _tree.expr.bin", &ex)) text.failparse("expression expected");
  auto dg = fastcast!(Delegate)(resolveType(ex.valueType()));
  if (!dg) text.failparse("__internal_flatten parameter is not delegate");
  auto args = dg.args();
  if (args.length != 1) text.failparse("__internal_flatten parameter has too many parts");
  auto arg = args[0];
  if (arg.initEx) text.failparse("__internal_flatten parameter has initializer");
  Argument[] resargs;
  if (auto tup = fastcast!(Tuple)(resolveType(arg.type))) {
    foreach (part; tup.types())
      resargs ~= Argument(part);
  } else {
    resargs ~= arg;
  }
  auto dg2 = fastalloc!(Delegate)(dg.ret(), resargs);
  return fastcast!(Object)(reinterpret_cast(dg2, ex));
}
mixin DefaultParser!(gotTerriblePapplyHack, "tree.expr.terrible_papply_hack", "3322", "__internal_flatten");

Object gotInternal(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.bin", &ex))
    t2.failparse("Expected expr string for internal lookup");
  opt(ex);
  auto t = fastcast!(StringExpr) (ex);
  if (!t)
    t2.failparse("Expected static string expr for internal lookup");
  auto p = t.str in internals;
  if (!p)
    t2.failparse(Format("No '", t.str, "' found in internals map! "));
  if (!*p)
    t2.failparse(Format("Result for '", t.str, "' randomly null! "));
  text = t2;
  return *p;
}
mixin DefaultParser!(gotInternal, "tree.expr.internal", "24052", "__internal");

import ast.pragmas;
static this() {
  pragmas["msg"] = delegate Object(Expr ex) {
    opt(ex);
    auto se = fastcast!(StringExpr) (ex);
    if (!se) throw new Exception(Format("Expected string expression for pragma(msg), not ", ex));
    logSmart!(false)("# ", se.str);
    return Single!(NoOp);
  };
  pragmas["fail"] = delegate Object(Expr ex) {
    opt(ex);
    auto se = fastcast!(StringExpr) (ex);
    if (!se) throw new Exception(Format("Expected string expression for pragma(fail), not ", ex));
    throw new Exception(se.str);
  };
}
