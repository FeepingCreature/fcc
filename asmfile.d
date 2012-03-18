module asmfile;

import optimizer_base, ast.base, parseBase: startsWith;
public import assemble;

const bool keepRegs = true, isForward = true;

import dwarf2;

import tools.log, tools.functional: map;
import tools.base: between, slice, split, stuple, apply, swap, Stuple;
const string[] utilRegs = ["%eax", "%ebx", "%ecx", "%edx"];
class AsmFile {
  string[] regs;
  string stackbase;
  static string number(int i) {
    if (isARM) return qformat("#", i);
    return qformat("$", i);
  }
  static string addressof(string s) {
    if (isARM) return qformat("=", s);
    else return qformat("$", s);
  }
  string id;
  int[string] globals;
  ubyte[][string] constants;
  string[][string] longstants; // sorry
  int[string] file_ids; // DWARF2 File IDs
  Stuple!(int, string)[string] globvars, tlsvars;
  int file_idcounter;
  bool[string] processorExtensions;
  bool[string] weaks; // symbols marked as weak
  Dwarf2Controller dwarf2;
  int getFileId(string name) {
    if (!name) name = "<nil>";
    if (auto ip = name in file_ids) return *ip;
    synchronized(this) {
      file_ids[name] = ++file_idcounter;
      return file_ids[name];
    }
  }
  void markWeak(string symbol) {
    weaks[symbol] = true;
  }
  void addTLS(string name, int size, string init) {
    if (!size) fail;
    tlsvars[name] = stuple(size, init);
  }
  string allocConstantValue(string name, ubyte[] data, bool forceAlloc = false) {
    if (data.length == 4 && !forceAlloc) {
      return qformat("$", (cast(int[]) data)[0]);
    }
    return allocConstant(name, data);
  }
  string allocConstant(string name, ubyte[] data, bool force = false) {
    if (!force)
      foreach (key, value; constants)
        if (value == data) return key;
    constants[name] = data;
    return name;
  }
  string allocLongstant(string name, string[] data, bool forceRealloc = false) {
    if (!forceRealloc)
      foreach (key, value; longstants)
        if (value == data) return key;
    longstants[name] = data;
    return name;
  }
  string[] codelines;
  bool optimize, debugMode, profileMode;
  this(bool optimize, bool debugMode, bool profileMode, string id) {
    New(cache);
    New(finalized);
    New(dwarf2);
    if (isARM) {
      regs = ["r0"[], "r1", "r2", "r3"].dup;
      stackbase = "fp";
    } else {
      regs = ["%eax"[], "%ebx", "%ecx", "%edx"].dup;
      stackbase = "%ebp";
    }
    this.optimize = optimize;
    this.debugMode = debugMode;
    this.profileMode = profileMode;
    this.id = id;
  }
  Transcache cache, finalized;
  final void add(ref Transaction t) {
    if (cache._list.length && cache.size == cache._list.length)
      flush;
    cache ~= t;
  }
  int currentStackDepth;
  void pushStack(string expr, int size) {
    if (isARM && (expr.find("%") != -1 || expr.find("$") != -1 || expr.find("=") != -1)) fail;
    if (isARM && size == 1) fail;
    willOverwriteComparison;
    Transaction t;
    t.kind = Transaction.Kind.Push;
    t.source = expr;
    t.size = size;
    t.stackdepth = currentStackDepth;
    add(t);
    currentStackDepth += size;
  }
  void popStack(string dest, int size) {
    if (isARM && dest.find("%") != -1) fail;
    willOverwriteComparison;
    Transaction t;
    t.kind = Transaction.Kind.Pop;
    t.dest = dest;
    t.size = size;
    t.stackdepth = currentStackDepth;
    add(t);
    currentStackDepth -= size;
  }
  void popStackDereference(string dest, int offset, int size) {
    if (isARM) {
      armpop(this, dest, size, offset);
    } else {
      popStack(qformat(offset, "(", dest, ")"), size);
    }
  }
  int checkptStack() {
    return currentStackDepth;
  }
  void restoreCheckptStack(int i, bool mayBeBigger = false /* used in loops/break/continue */) {
    if (!mayBeBigger && currentStackDepth < i) {
      logln("Tried to unwind stack while unwound further - logic error while restoring ", currentStackDepth, " to ", i);
      fail;
    }
    sfree(currentStackDepth - i);
  }
  void nvm(string mem) {
    Transaction t;
    t.kind = Transaction.Kind.Nevermind;
    t.dest = mem;
    add(t);
  }
  void nvmRegisters() {
    foreach (reg; utilRegs)
      nvm(reg);
  }
  void compare(string op1, string op2, bool test = false) {
    Transaction t;
    t.kind = Transaction.Kind.Compare;
    if (isARM) {
      t.op1 = op1; t.op2 = op2;
    } else {
      t.op1 = op2; t.op2 = op1;
    }
    t.test = test;
    add(t);
    comparisonState = true;
  }
  // migratory move; contents of source become irrelevant
  void mmove4(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.Mov;
    t.from = from; t.to = to;
    add(t);
  }
  void mmove2(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.Mov2;
    t.from = from; t.to = to;
    add(t);
  }
  void mmove1(string from, string to) {
    if (isARM && (from.find("sp") != -1 || to.find("sp") != -1) && currentStackDepth % 4) fail;
    Transaction t;
    t.kind = Transaction.Kind.Mov1;
    t.from = from; t.to = to;
    add(t);
  }
  void movd(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.MovD;
    t.from = from; t.to = to;
    add(t);
  }
  void loadAddress(string mem, string to) {
    Transaction t;
    t.kind = Transaction.Kind.LoadAddress;
    t.from = mem; t.to = to;
    add(t);
  }
  void loadOffsetAddress(string reg, int offset, string to) {
    if (isARM) {
      loadAddress(qformat("[", reg, ",#", offset, "]"), to);
    } else {
      loadAddress(qformat(offset, "(", reg, ")"), to);
    }
  }
  void salloc(int sz) { // alloc stack space
    willOverwriteComparison;
    Transaction t;
    currentStackDepth += sz;
    t.kind = Transaction.Kind.SAlloc;
    t.size = sz;
    add(t);
  }
  void sfree(int sz) { // alloc stack space
    willOverwriteComparison;
    Transaction t;
    currentStackDepth -= sz;
    t.kind = Transaction.Kind.SFree;
    t.size = sz;
    add(t);
  }
  import tools.ctfe;
  const string JumpTable = `
    cond | jump |  cmov  |floatjump| floatmov | armjump | armcmov
    -----+------+--------+---------+----------+---------+--------
    fff  |      |        |         |          |         |
    fft  | jg   | cmovg  | ja      | cmova    | bgt     | movgt
    ftf  | je   | cmove  | je      | cmove    | beq     | moveq
    ftt  | jge  | cmovge | jae     | cmovae   | bge     | movge
    tff  | jl   | cmovl  | jb      | cmovb    | blt     | movlt
    tft  | jne  | cmovne | jne     | cmovne   | bne     | movne
    ttf  | jle  | cmovle | jbe     | cmovbe   | ble     | movle
    ttt  | jmp  | mov    | jmp     | mov      | b       | mov
  `;
  bool[string] jumpedForwardTo; // Emitting a forward label that hasn't been jumped to is redundant.
  void markLabelInUse(string label) {
    jumpedForwardTo[label] = true;
  }
  void jumpOn(bool smaller, bool equal, bool greater, string label) {
    comparisonState = false;
    markLabelInUse(label);
    labels_refcount[label]++;
    // TODO: unsigned?
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$jump".length) if (isARM) jump(label, false, "$armjump"); else jump(label, false, "$jump"); return; }
    `));
    throw new Exception(Format(
      "Impossibility yay (", smaller, ", ", equal, ", ", greater, ")"
    ));
  }
  void cmov(bool smaller, bool equal, bool greater, string from, string to) {
    comparisonState = false;
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$cmov".length) if (isARM) put("$armcmov ", to, ", ", from); else put("$cmov ", from, ", ", to); return; }
    `));
    throw new Exception(Format(
      "Impossibility yay (", smaller, ", ", equal, ", ", greater, ")"
    ));
  }
  void jumpOnFloat(bool smaller, bool equal, bool greater, string label, bool convert = true) {
    comparisonState = false;
    markLabelInUse(label);
    labels_refcount[label]++;
    nvm("%eax");
    if (convert) {
      put("fnstsw %ax");
      put("sahf");
    }
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$floatjump".length) jump(label, false, "$floatjump"); return; }
    `));
  }
  void moveOnFloat(bool smaller, bool equal, bool greater, string from, string to, bool convert = true) {
    comparisonState = false;
    nvm("%eax");
    if (convert) {
      put("fnstsw %ax");
      put("sahf");
    }
    mixin(JumpTable.ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { static if ("$floatmov".length) put("$floatmov ", from, ", ", to); return; }
    `));
  }
  void mathOp(string which, string op1, string op2, string op3 = null) {
    Transaction t;
    t.kind = Transaction.Kind.MathOp;
    t.opName = which;
    t.op1 = op1; t.op2 = op2; t.op3 = op3;
    add(t);
  }
  void SSEOp(string which, string op1, string op2, bool ignoreStackAlignment = false /* true for movd */) {
    if ((op1 == "(%esp)" || op2 == "(%esp)") && currentStackDepth%16 != 0 && !ignoreStackAlignment) {
      logln("stack misaligned for SSE");
      fail;
    }
    Transaction t;
    t.kind = Transaction.Kind.SSEOp;
    t.opName = which;
    t.op1 = op1; t.op2 = op2;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void extendDivide(string src, bool signed) {
    Transaction t;
    t.kind = Transaction.Kind.ExtendDivide;
    t.source = src;
    t.signed = signed;
    add(t);
  }
  void call(string what) {
    Transaction t;
    t.kind = Transaction.Kind.Call;
    t.dest = what;
    add(t);
  }
  void swap(string op1, string op2, int size = 4) {
    Transaction t;
    t.kind = Transaction.Kind.Swap;
    t.source = op1;
    t.dest = op2;
    t.size = size;
    add(t);
  }
  int floatStackDepth;
  void incFloatStack() {
    floatStackDepth ++;
    if (floatStackDepth == 8)
      throw new Exception("Floating point stack overflow .. that was unexpected. Simplify your expressions. ");
  }
  void loadFloat(string mem) {
    if (isARM) fail;
    incFloatStack();
    Transaction t;
    t.kind = Transaction.Kind.FloatLoad;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void loadDouble(string mem) {
    incFloatStack();
    Transaction t;
    t.kind = Transaction.Kind.DoubleLoad;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void loadIntAsFloat(string mem) {
    incFloatStack();
    Transaction t;
    t.kind = Transaction.Kind.FloatIntLoad;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void loadLongAsFloat(string mem) {
    incFloatStack();
    Transaction t;
    t.kind = Transaction.Kind.FloatLongLoad;
    t.source = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void storeFloat(string mem) {
    floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.FloatPop;
    t.dest = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void storeFPAsInt(string mem) {
    floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.FPIntPop;
    t.dest = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void storeFPAsLong(string mem) {
    floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.FPLongPop;
    t.dest = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void storeDouble(string mem) {
    floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.DoublePop;
    t.dest = mem;
    t.stackdepth = currentStackDepth;
    add(t);
  }
  void compareFloat(string mem, bool useIVariant) {
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
    t.useIVariant = useIVariant;
    add(t);
    comparisonState = true;
  }
  void fpuToStack() {
    salloc(8);
    storeDouble("(%esp)");
  }
  void stackToFpu() {
    loadDouble("(%esp)");
    sfree(8);
  }
  void floatMath(string op, bool consumesStack = true) {
    if (consumesStack) floatStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.FloatMath;
    t.opName = op;
    add(t);
  }
  void fpuOp(string opname) {
    Transaction t;
    t.kind = Transaction.Kind.PureFloat;
    t.opName = opname;
    add(t);
  }
  int labelCounter; // Limited to 2^31 labels, le omg.
  string genLabel() {
    return qformat(".Label", labelCounter++);
  }
  void jump(string label, bool keepRegisters = false, string mode = null) {
    comparisonState = false;
    markLabelInUse(label);
    labels_refcount[label] ++;
    Transaction t;
    t.kind = Transaction.Kind.Jump;
    t.dest = label;
    t.mode = mode;
    t.keepRegisters = keepRegisters;
    add(t);
  }
  void emitLabel(string name, bool keepregs = false, bool isforward = false) {
    if (isforward && !(name in jumpedForwardTo)) return;
    Transaction t;
    t.kind = Transaction.Kind.Label;
    t.keepRegisters = keepregs;
    t.names ~= name;
    add(t);
  }
  int[string] labels_refcount;
  // no jumps past this point
  // removes unused labels
  void jump_barrier() { }
  /+void jump_barrier() {
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
  }+/
  int lastStackDepth;
  void comment(T...)(T t) {
    if (!optimize) {
      string comment = "#";
      if (isARM) comment = "@";
      put(comment, " [", currentStackDepth, ": ", currentStackDepth - lastStackDepth, "]: ", t);
    }
    lastStackDepth = currentStackDepth;
  }
  string[] goodOpts;
  bool[string] unused;
  bool delegate(Transcache, ref int[string])[string] map;
  import tools.threads: SyncObj;
  void runOpts() {
    string[] newOpts;
    if (debugOpts) {
      foreach (entry; opts) if (entry._2) {
        unused[entry._1] = true;
        map[entry._1] = entry._0;
      }
      foreach (opt; goodOpts) {
        unused.remove(opt);
        map[opt](cache, labels_refcount);
      }
    }
    // ext_step(cache, labels_refcount); // run this first
    while (true) {
      bool anyChange;
      foreach (entry; opts) if (entry._2) {
        auto opt = entry._0, name = entry._1;
        if (opt(cache, labels_refcount)) {
          if (false && debugOpts) { // causes difference in assembly .. somehow. wtf? todo!
            unused.remove(name);
            newOpts ~= name;
            goodOpts ~= name;
          }
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
    if (optimize) {
      auto full_list = cache;
      New(cache);
      void flush2(Transaction* entry = null) {
        runOpts;
        finalized ~= cache.list();
        if (entry) finalized ~= *entry;
        cache.clear;
      }
      outer:while (full_list.list().length) {
        foreach (i, entry; full_list.list()) {
          if (entry.kind != Transaction.Kind.Text) {
            cache ~= entry;
          } else {
            flush2(&entry);
            full_list._list = full_list._list[i+1 .. $];
            full_list.size -= i+1;
            continue outer;
          }
        }
        break;
      }
      flush2;
    }
    foreach (entry; finalized.list) if (auto line = entry.toAsm()) _put(line);
    foreach (entry; cache.list)     if (auto line = entry.toAsm()) _put(line);
    finalized.clear;
    cache.clear;
  }
  void put(T...)(T t) {
    Transaction tn;
    tn.kind = Transaction.Kind.Text;
    tn.text = qformat(t);
    add(tn);
  }
  /*void put(T...)(T t) {
    flush();
    _put(t);
  }*/
  void _put(T...)(T t) {
    codelines ~= qformat(t, "\n");
  }
  void genAsm(void delegate(string) dg) {
    flush();
    dg(".section\t.debug_line\n");
    dg(".Ldebug_line0:\n");
    if (isARM) {
      dg(".cpu\tarm9tdmi\n.fpu\tsoftvfp\n");
      foreach (pair; [[20,1],[21,1],[23,3],[24,1],[25,1],[26,2],[30,6],[18,4]]) {
        dg(qformat(".eabi_attribute ", pair[0], ", ", pair[1], "\n"));
      }
    }
    dg(qformat(".file \"", id, "\"\n"));
    foreach (name, data; globvars) {
      dg(qformat(".comm\t", name, ",", data._0, "\n"));
      assert(!data._1, "4");
    }
    dg(".section\t.data,\"aw\"\n");
    dg(".weak _sys_tls_data_start\n");
    dg(".globl _sys_tls_data_start\n");
    dg("_sys_tls_data_start:\n");
    string id2 = id[0..$-3].replace("/", "_").replace("-", "_dash_");
    dg(".globl _sys_tls_data_"); dg(id2); dg("_start\n");
    dg("_sys_tls_data_"); dg(id2); dg("_start:\n");
    foreach (name, bogus; weaks) {
      dg(qformat(".weak ", name, "\n"));
    }
    foreach (name, data; tlsvars) {
      auto alignment = data._0;
      if (alignment >= 16) alignment = 16;
      else {
        if (alignment > 8) alignment = 8;
      }
      dg(qformat("\t.balign ", alignment, "\n"));
      dg("\t.globl "); dg(name); dg("\n");
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
    dg(".globl _sys_tls_data_"); dg(id2); dg("_end\n");
    dg("_sys_tls_data_"); dg(id2); dg("_end:\n");
    
    if (!isARM) dg(".section\t.rodata\n");
    foreach (name, c; constants) {
      if (c.length > 4) dg(".balign 16\n");
      dg(".globl "); dg(name); dg("\n");
      dg(name); dg(":\n");
      while (c.length) {
        auto part = c;
        if (part.length > 128) { part = part[0..128]; c = c[128 .. $]; }
        else { c = null; }
        dg(".byte ");
        foreach (i, val; part) {
          if (i) dg(", ");
          dg(qformat(cast(ubyte) val));
        }
        dg("\n");
      }
      dg(".byte 0\n");
      // not win32 compatible
      // dg(".local "); dg(name); dg("\n");
    }
    foreach (name, array; longstants) { // lol
      if (array.length >= 4) dg(".balign 16\n");
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
    dg(".Ltext:\n");
    foreach (line; codelines)
      dg(line);
    dg(".Letext:\n");
    foreach (line; dwarf2.genData()) {
      dg(line); dg("\n");
    }
  }
  void pool() {
    put("b 0f");
    put(".ltorg");
    put("0:");
  }
  // is cpu in post-comparison state?
  // disallow some operations (math) that woukld
  // overwrite it before the next branch
  bool comparisonState;
  final void willOverwriteComparison() {
    if (!comparisonState) return;
    logln("Cannot proceed: would overwrite comparison results! ");
    fail;
  }
}
