module asmfile;

import optimizer, ast.types, ast.base, parseBase: startsWith;
public import assemble;

import tools.log, tools.functional: map;
import tools.base: between, slice, atoi, split, stuple, apply, swap;
const string[] utilRegs = ["%eax", "%ebx", "%ecx", "%edx"];
class AsmFile {
  string id;
  int[string] globals;
  ubyte[][string] constants;
  string[][string] longstants; // sorry
  int[string] file_ids; // DWARF2 File IDs
  Stuple!(int, string)[string] globvars, tlsvars;
  int file_idcounter;
  int getFileId(string name) {
    if (auto ip = name in file_ids) return *ip;
    synchronized(this) {
      file_ids[name] = ++file_idcounter;
      return file_ids[name];
    }
  }
  void addTLS(string name, int size, string init) {
    if (!size) asm { int 3; }
    tlsvars[name] = stuple(size, init);
  }
  string allocConstant(string name, ubyte[] data) {
    foreach (key, value; constants)
      if (value == data) return key;
    constants[name] = data;
    return name;
  }
  string allocLongstant(string name, string[] data) {
    foreach (key, value; longstants)
      if (value == data) return key;
    longstants[name] = data;
    return name;
  }
  string code;
  bool optimize;
  this(bool optimize, string id) { New(cache); New(finalized); this.optimize = optimize; this.id = id; }
  Transcache cache, finalized;
  int currentStackDepth;
  void pushStack(string expr, IType type) {
    Transaction t;
    t.kind = Transaction.Kind.Push;
    t.source = expr;
    t.type = type;
    t.stackdepth = currentStackDepth;
    cache ~= t;
    currentStackDepth += type.size;
  }
  void popStack(string dest, IType type) {
    Transaction t;
    t.kind = Transaction.Kind.Pop;
    t.dest = dest;
    t.type = type;
    t.stackdepth = currentStackDepth;
    cache ~= t;
    currentStackDepth -= type.size;
  }
  int checkptStack() {
    return currentStackDepth;
  }
  void restoreCheckptStack(int i, bool mayBeBigger = false /* used in loops/break/continue */) {
    if (!mayBeBigger && currentStackDepth < i) {
      logln("Tried to unwind stack while unwound further - logic error while restoring ", currentStackDepth, " to ", i);
      asm { int 3; }
    }
    sfree(currentStackDepth - i);
  }
  void nvm(string mem) {
    Transaction t;
    t.kind = Transaction.Kind.Nevermind;
    t.dest = mem;
    cache ~= t;
  }
  void nvmRegisters() {
    foreach (reg; utilRegs)
      nvm(reg);
  }
  void compare(string op1, string op2, bool test = false) {
    Transaction t;
    t.kind = Transaction.Kind.Compare;
    t.op1 = op1; t.op2 = op2;
    t.test = test;
    cache ~= t;
  }
  // migratory move; contents of source become irrelevant
  void mmove4(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.Mov;
    t.from = from; t.to = to;
    cache ~= t;
  }
  void mmove2(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.Mov2;
    t.from = from; t.to = to;
    cache ~= t;
  }
  void mmove1(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.Mov1;
    t.from = from; t.to = to;
    cache ~= t;
  }
  void movd(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.MovD;
    t.from = from; t.to = to;
    cache ~= t;
  }
  void loadAddress(string mem, string to) {
    Transaction t;
    t.kind = Transaction.Kind.LoadAddress;
    t.from = mem; t.to = to;
    cache ~= t;
  }
  void salloc(int sz) { // alloc stack space
    Transaction t;
    currentStackDepth += sz;
    t.kind = Transaction.Kind.SAlloc;
    t.size = sz;
    cache ~= t;
  }
  void sfree(int sz) { // alloc stack space
    Transaction t;
    currentStackDepth -= sz;
    t.kind = Transaction.Kind.SFree;
    t.size = sz;
    cache ~= t;
  }
  import tools.ctfe;
  const string JumpTable = `
    cond | jump |  cmov  |floatjump| floatmov
    -----+------+--------+---------+---------
    fff  |      |        |         | 
    fft  | jg   | cmovg  | ja      | cmova
    ftf  | je   | cmove  | je      | cmove
    ftt  | jge  | cmovge | jae     | cmovae
    tff  | jl   | cmovl  | jb      | cmovb
    tft  | jne  | cmovne | jne     | cmovne
    ttf  | jle  | cmovle | jbe     | cmovbe
    ttt  | jmp  | mov    | jmp     | mov
  `;
  void jumpOn(bool smaller, bool equal, bool greater, string label) {
    labels_refcount[label]++;
    // TODO: unsigned?
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$jump".length) put("$jump ", label); return; }
    `));
    throw new Exception(Format(
      "Impossibility yay (", smaller, ", ", equal, ", ", greater, ")"
    ));
  }
  void cmov(bool smaller, bool equal, bool greater, string from, string to) {
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$cmov".length) put("$cmov ", from, ", ", to); return; }
    `));
    throw new Exception(Format(
      "Impossibility yay (", smaller, ", ", equal, ", ", greater, ")"
    ));
  }
  void jumpOnFloat(bool smaller, bool equal, bool greater, string label) {
    labels_refcount[label]++;
    nvm("%eax");
    put("fnstsw %ax");
    put("sahf");
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$floatjump".length) put("$floatjump ", label); return; }
    `));
  }
  void moveOnFloat(bool smaller, bool equal, bool greater, string from, string to) {
    nvm("%eax");
    put("fnstsw %ax");
    put("sahf");
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$floatmov".length) put("$floatmov ", from, ", ", to); return; }
    `));
  }
  void mathOp(string which, string op1, string op2) {
    Transaction t;
    t.kind = Transaction.Kind.MathOp;
    t.opName = which;
    t.op1 = op1; t.op2 = op2;
    cache ~= t;
  }
  void SSEOp(string which, string op1, string op2) {
    if ((op1 == "(%esp)" || op2 == "(%esp)") && currentStackDepth%16 != 0) {
      logln("stack misaligned for SSE");
      asm { int 3; }
    }
    Transaction t;
    t.kind = Transaction.Kind.SSEOp;
    t.opName = which;
    t.op1 = op1; t.op2 = op2;
    t.stackdepth = currentStackDepth;
    cache ~= t;
  }
  void extendDivide(string src) {
    Transaction t;
    t.kind = Transaction.Kind.ExtendDivide;
    t.source = src;
    cache ~= t;
  }
  void call(string what) {
    Transaction t;
    t.kind = Transaction.Kind.Call;
    t.dest = what;
    cache ~= t;
  }
  int floatStackDepth;
  void incFloatStack() {
    floatStackDepth ++;
    if (floatStackDepth == 8)
      throw new Exception("Floating point stack overflow .. that was unexpected. Simplify your expressions. ");
  }
  void loadFloat(string mem) {
    incFloatStack();
    Transaction t;
    t.kind = Transaction.Kind.FloatLoad;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    cache ~= t;
  }
  void loadDouble(string mem) {
    incFloatStack();
    Transaction t;
    t.kind = Transaction.Kind.DoubleLoad;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    cache ~= t;
  }
  void loadIntAsFloat(string mem) {
    incFloatStack();
    Transaction t;
    t.kind = Transaction.Kind.FloatIntLoad;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    cache ~= t;
  }
  void storeFloat(string mem) {
    floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.FloatPop;
    t.dest = mem;
    t.stackdepth = currentStackDepth;
    cache ~= t;
  }
  void storeDouble(string mem) {
    floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.DoublePop;
    t.dest = mem;
    t.stackdepth = currentStackDepth;
    cache ~= t;
  }
  void compareFloat(string mem) {
    bool isReg;
    if (mem.startsWith("%st")) {
      isReg = true;
    }
    floatStackDepth --;
    if (isReg) floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.FloatCompare;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    cache ~= t;
  }
  void fpuToStack() {
    salloc(8);
    storeDouble("(%esp)");
  }
  void stackToFpu() {
    loadDouble("(%esp)");
    sfree(8);
  }
  void floatMath(string op) {
    floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.FloatMath;
    t.opName = op;
    cache ~= t;
  }
  void swapFloats() {
    Transaction t;
    t.kind = Transaction.Kind.FPSwap;
    cache ~= t;
  }
  int labelCounter; // Limited to 2^31 labels, le omg.
  string genLabel() {
    return qformat(".Label", labelCounter++);
  }
  void jump(string label, bool keepRegisters = false) {
    labels_refcount[label] ++;
    Transaction t;
    t.kind = Transaction.Kind.Jump;
    t.dest = label;
    t.keepRegisters = keepRegisters;
    cache ~= t;
  }
  void emitLabel(string name, bool keepregs = false) {
    Transaction t;
    t.kind = Transaction.Kind.Label;
    t.keepRegisters = keepregs;
    t.names ~= name;
    cache ~= t;
  }
  int[string] labels_refcount;
  // no jumps past this point
  // removes unused labels
  void jump_barrier() {
    if (optimize) runOpts; // clean up
    Transaction[] newlist;
    /*foreach (t; cache.list) {
      if (t.kind != Transaction.Kind.Label) newlist ~= t;
      else
        foreach (name; t.names)
          if (name in labels_refcount && labels_refcount[name] > 0) { newlist ~= t; break; }
    }*/
    newlist = cache.list();
    finalized ~= newlist;
    
    cache.clear;
    labels_refcount = null;
  }
  int lastStackDepth;
  void comment(T...)(T t) {
    if (!optimize) {
      put("# [", currentStackDepth, ": ", currentStackDepth - lastStackDepth, "]: ", t);
    }
    lastStackDepth = currentStackDepth;
  }
  static string[] goodOpts;
  import tools.threads: SyncObj;
  void runOpts() {
    setupOpts;
    string[] newOpts;
    static bool[string] unused;
    static bool delegate(Transcache, ref int[string])[string] map;
    synchronized(SyncObj!(unused))
    synchronized(SyncObj!(map))
      foreach (entry; opts) if (entry._2) {
        unused[entry._1] = true;
        map[entry._1] = entry._0;
      }
    // LOL
    synchronized(SyncObj!(goodOpts))
    synchronized(SyncObj!(unused))
    synchronized(SyncObj!(map))
      foreach (opt; goodOpts) {
        unused.remove(opt);
        map[opt](cache, labels_refcount);
      }
    // ext_step(cache, labels_refcount); // run this first
    while (true) {
      bool anyChange;
      synchronized(SyncObj!(goodOpts))
      synchronized(SyncObj!(unused))
      foreach (entry; opts) if (entry._2) {
        auto opt = entry._0, name = entry._1;
        if (opt(cache, labels_refcount)) {
          unused.remove(name);
          newOpts ~= name;
          goodOpts ~= name;
          anyChange = true;
        }
        // logln("Executed ", name, " => ", anyChange, "; ", cache.list.length);
      }
      // logln("::", anyChange, "; ", cache.list);
      if (!anyChange) break;
    }
    if (debugOpts) {
      foreach (opt; newOpts)
        log("[", unique(opt), "]");
    }
      
    string join(string[] s) {
      string res;
      foreach (str; s) { if (res) res ~= ", "; res ~= str; }
      return res;
    }
    if (newOpts && debugOpts) {
      logln("Opt: ", goodOpts.join(), " + ", newOpts/+, " - ", unused.keys+/);
      logln("Unused: ", unused.keys);
    }
  }
  void flush() {
    if (optimize) runOpts;
    foreach (entry; finalized.list) if (auto line = entry.toAsm()) _put(line);
    foreach (entry; cache.list)     if (auto line = entry.toAsm()) _put(line);
    finalized.clear;
    cache.clear;
  }
  void put(T...)(T t) {
    flush();
    _put(t);
  }
  void _put(T...)(T t) {
    code ~= qformat(t, "\n");
  }
  void genAsm(void delegate(string) dg) {
    flush();
    dg(qformat(".file \"", id, "\"\n"));
    foreach (name, data; globvars) {
      dg(qformat(".comm\t", name, ",", data._0, "\n"));
      assert(!data._1, "4");
    }
    dg(".section\t.data,\"aw\"\n");
    dg(".weak _sys_tls_data_start\n");
    dg(".globl _sys_tls_data_start\n");
    dg("_sys_tls_data_start:\n");
    dg(".globl _sys_tls_data_"); dg(id); dg("_start\n");
    dg("_sys_tls_data_"); dg(id); dg("_start:\n");
    foreach (name, data; tlsvars) {
      auto alignment = data._0;
      if (alignment >= 16) alignment = 16;
      else {
        if (alignment > 8) alignment = 16;
      }
      dg(qformat("\t.align ", alignment, "\n"));
      dg("\t.globl "); dg(name); dg("\n");
      // dg(qformat("\t.type ", name, "\n"));
      // dg(qformat("\t.size ", name, ", ", data._0, "\n"));
      dg("\t"); dg(name); dg(":\n");
      if (data._1) {
        auto parts = data._1.split(",");
        assert(parts.length * nativePtrSize == data._0,
                qformat("Length mismatch: ", parts.length, " * ", 
                      nativePtrSize, " != ", data._0, " for ", data._1));
        dg("\t.long ");
        foreach (i, part; parts) {
          if (i) dg(", ");
          dg(part);
        }
        dg("\n");
      } else { // zeroes
        dg(qformat("\t.fill ", data._0, ", 1\n"));
      }
    }
    dg(".globl _sys_tls_data_"); dg(id); dg("_end\n");
    dg("_sys_tls_data_"); dg(id); dg("_end:\n");
    
    dg(".section\t.rodata\n");
    foreach (name, c; constants) {
      dg(name); dg(":\n");
      dg(".byte ");
      foreach (val; c) dg(qformat(cast(ubyte) val, ", "));
      dg("0\n");
      // not win32 compatible
      // dg(".local "); dg(name); dg("\n");
    }
    foreach (name, array; longstants) { // lol
      dg(name); dg(":\n");
      dg(".long ");
      foreach (val; array) dg(qformat(val, ", "));
      dg("0\n");
      dg(".global "); dg(name); dg("\n");
    }
    foreach (key, value; file_ids) {
      dg(qformat(".file ", value, " \"", key, "\"\n"));
    }
    dg(".text\n");
    dg(code);
  }
}
