module ast.intrinsic;

import ast.modules, ast.pointer, ast.base, ast.oop, ast.casting;
// not static this() to work around a precedence bug in phobos. called from main.
void setupSysmods() {
  if (sysmod) return;
  string src = `
    module sys;
    pragma(lib, "m");
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
      // printf("memcpy(%p, %p, %i)\n", dest, src, n);
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
    template sys_array_cast(T) {
      template sys_array_cast(U) {
        T sys_array_cast(U u) {
          alias ar = u[0];
          alias sz1 = u[1];
          alias sz2 = u[2];
          auto destlen = ar.length * sz1;
          if destlen % sz2 {
            writeln "Array cast failed: size/alignment mismatch - casting $(string-of U[0]) of $(size-of U[0]) to $(string-of T) of $(size-of T) (u of $(u[(1, 2)]) for $(ar.length) => $(destlen) => $(destlen % 1)). ";
            _interrupt 3;
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
    alias vec2i = vec(int, 2);
    alias vec3i = vec(int, 3);
    alias vec4i = vec(int, 4);
    string ptoa(void* p) {
      auto res = new char[]((size-of size_t) * 2 + 2 + 1);
      snprintf(res.ptr, res.length, "0x%08x", p); // TODO: adapt for 64-bit
      return res[0 .. res.length - 1];
    }
    void writeln(string line) {
      printf("%.*s\n", line.length, line.ptr);
    }
    string dtoa(double d) {
      auto res = new char[] 128; // yes, actually does need to be this big >_>
      int len = snprintf(res.ptr, res.length, "%f", d);
      if len > res.length len = res.length;
      return res[0 .. len];
    }
    string ftoa(float f) {
      short backup = fpucw;
      fpucw = short:(fpucw | 0b111_111); // mask nans
      string res = dtoa double:f;
      fpucw = backup;
      return res;
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
    class Error {
      string msg;
      void init(string s) msg = s;
      string toString() { return "Error: $msg"; }
    }
    class Signal : Error {
      void init(string s) { super.init s; }
    }
    void raise-signal(Signal sig) {
      auto cur = __hdl__;
      while cur {
        if cur.accepts(sig) cur.dg(sig);
        cur = cur.prev;
      }
    }
    void raise-error(Error err) {
      auto cur = __hdl__;
      while cur {
        if cur.accepts(err) cur.dg(err);
        cur = cur.prev;
      }
      writeln "Unhandled condition: $(err.toString()). ";
      _interrupt 3;
    }
    class MissedReturnError : Error {
      void init(string name) { super.init("End of $name reached without return"); }
    }
    void[] dupvcache;
    alias BLOCKSIZE = 16384;
    void missed_return(string name) {
      raise-error new MissedReturnError name;
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
    int fastfloor(float f) {
      alias magicdelta = 0.000000015;
      alias roundeps = 0.5 - magicdelta;
      alias magic = 6755399441055744.0;
      double d = double:f - roundeps + magic;
      return (int*:&d)[0];
    }
    void fastfloor3f(vec3f v, vec3i* res) {
      (vec4f*: &v).w = 0; // prevent fp error
      xmm[4] = v;
      asm "cvttps2dq %xmm4, %xmm5";`"
      asm `psrld $31, %xmm4`;"`
      asm "psubd %xmm4, %xmm5";
      *res = vec3i:xmm[5];
    }
    struct RefCounted {
      void delegate() onZero;
      int refs;
      void claim() { refs ++; }
      void release() { refs --; if !refs onZero(); }
    }
    string replace(string source, string what, string with) {
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
      string name;
      void* dataStart, dataEnd;
      bool compiled; // does this have an .o file?
      void function()[auto~] constructors;
      bool constructed;
      string[] _imports;
      ModuleInfo[auto~] imports;
    }
    ModuleInfo[auto~] __modules;
    ModuleInfo lookupInfo(string name) {
      for auto mod <- __modules if mod.name == name return mod;
      raise-error new Error "No such module: $name";
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
    int main2(int argc, char** argv) {
      __setupModuleInfo();
      constructModules();
      
      mxcsr |= (1 << 6) | (3 << 13) | (1 << 15); // Denormals Are Zero; Round To Zero; Flush To Zero.
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
        // system("gdb /proc/self/exe -p \$(/proc/self/stat |awk '{print \$1}')");
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
        bool advance() { raise-error new Error "Iterator::advance() not implemented! "; }
      }
    }
    class AssertError : Error {
      void init(string s) super.init "AssertError: $s";
    }
    void assert(bool cond, string mesg = string:null) {
      if (!cond)
        if (mesg) raise-error new AssertError mesg;
        else raise-error new AssertError "Assertion failed! ";
    }
  `.dup; // make sure we get different string on subsequent calls
  synchronized(SyncObj!(sourcefiles))
    sourcefiles["<internal:sys>"] = src;
  sysmod = fastcast!(Module) (parsecon.parse(src, "tree.module"));
  sysmod.splitIntoSections = true;
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
    left ~= mod.getImports();
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
  auto decl = new VarDecl;
  decl.vars ~= var;
  decl.vars ~= count;
  sc.addStatement(decl);
  
  auto backupmod = current_module();
  scope(exit) current_module.set(backupmod);
  current_module.set(sysmod);
  
  foreach (mod; list) {
    auto fltname = mod.name.replace(".", "_").replace("-", "_dash_");
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
             (`{var = new ModuleInfo;
               __modules ~= var;
               var.name = name;
               var.dataStart = symdstart;
               var.dataEnd = symdend;
               var.compiled = bool:compiled;
             }` , "var", var, "name", mkString(mod.name),
                  "symdstart", symdstart,
                  "symdend", symdend,
                  "compiled", compiled
            )
    );
    foreach (fun; mod.constrs) {
      sc.addStatement(
        iparse!(Statement, "init_mod_constr", "tree.stmt")
               (`var.constructors ~= fun;
               `, "var", var, "fun", new FunRefExpr(fun))
      );
    }
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
    foreach (mod2; imps) {
      sc.addStatement(
        iparse!(Statement, "init_mod_imports", "tree.stmt")
               (`var._imports[c++] = mod2;`, sc,
                "var", var, "c", count, "mod2", mkString(mod2.name)));
    }
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
    void emitAsm(AsmFile af) { af.pushStack(reg, nativePtrSize); }
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
  // Link with this library
  pragmas["msg"] = delegate Object(Expr ex) {
    ex = foldex(ex);
    auto se = fastcast!(StringExpr) (ex);
    if (!se) throw new Exception("Expected string expression for pragma(msg)! ");
    logln("# ", se.str);
    return Single!(NoOp);
  };
}
