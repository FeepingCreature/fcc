module asmfile;

import assemble, optimizer, ast.types, parseBase: startsWith;

import tools.log, tools.functional: map;
import tools.base: between, slice, atoi, split, stuple, apply, swap;
class AsmFile {
  string id;
  int[string] globals;
  ubyte[][string] constants;
  string[][string] longstants; // sorry
  int[string] uninit_tlsvars; // different segment in ELF
  Stuple!(int, string)[string] globvars, tlsvars;
  void addTLS(string name, int size, string init) {
    if (init) tlsvars[name] = stuple(size, init);
    else uninit_tlsvars[name] = size;
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
    currentStackDepth -= type.size;
    Transaction t;
    t.kind = Transaction.Kind.Pop;
    t.dest = dest;
    t.type = type;
    cache ~= t;
  }
  int checkptStack() {
    return currentStackDepth;
  }
  void restoreCheckptStack(int i, bool mayBeBigger = false /* used in loops/break/continue */) {
    if (!mayBeBigger && currentStackDepth < i) {
      logln("Tried to unwind stack while unwound further - logic error");
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
  void jumpOn(bool smaller, bool equal, bool greater, string label) {
    labels_refcount[label]++;
    // TODO: unsigned?
    mixin(`
      cond | instruction
       fff | nop
       fft | jg dest
       ftf | je dest
       ftt | jge dest
       tff | jl dest
       tft | jne dest
       ttf | jle dest
       ttt | jmp dest`
      .ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { put("$instruction".replace("dest", label)); return; }
    `));
    throw new Exception(Format(
      "Impossibility yay (", smaller, ", ", equal, ", ", greater, ")"
    ));
  }
  void jumpOnFloat(bool smaller, bool equal, bool greater, string label) {
    labels_refcount[label]++;
    put("fnstsw %ax");
    put("sahf");
    mixin(`
      cond | instruction
       fff | xorb %al, %al
       fft | seta %al
       ftf | sete %al
       ftt | setae %al
       tff | setb %al
       tft | setne %al
       ttf | setbe %al
       ttt | movb $1, %al`
      .ctTableUnroll(`
        if (
          (("$cond"[0] == 't') == smaller) &&
          (("$cond"[1] == 't') == equal) &&
          (("$cond"[2] == 't') == greater)
        ) { put("$instruction"); }
    `));
    put("testb %al, %al");
    put("jne ", label);
  }
  void mathOp(string which, string op1, string op2) {
    Transaction t;
    t.kind = Transaction.Kind.MathOp;
    t.opName = which;
    t.op1 = op1; t.op2 = op2;
    cache ~= t;
  }
  void call(string what) {
    Transaction t;
    t.kind = Transaction.Kind.Call;
    t.dest = what;
    cache ~= t;
  }
  int floatStackDepth;
  void loadFloat(string mem) {
    floatStackDepth ++;
    if (floatStackDepth == 8)
      throw new Exception("Floating point stack overflow .. that was unexpected. Simplify your expressions. ");
    Transaction t;
    t.kind = Transaction.Kind.FloatLoad;
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
  void floatToStack() {
    salloc(4);
    storeFloat("(%esp)");
  }
  void stackToFloat() {
    loadFloat("(%esp)");
    sfree(4);
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
    t.kind = Transaction.Kind.FloatSwap;
    cache ~= t;
  }
  int labelCounter; // Limited to 2^31 labels, le omg.
  string genLabel() {
    return Format(".Label", labelCounter++);
  }
  void jump(string label) {
    labels_refcount[label] ++;
    Transaction t;
    t.kind = Transaction.Kind.Jump;
    t.dest = label;
    cache ~= t;
  }
  void emitLabel(string name) {
    Transaction t;
    t.kind = Transaction.Kind.Label;
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
    if (!optimize)
      put("# [", currentStackDepth, ": ", currentStackDepth - lastStackDepth, "]: ", t);
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
        // logln("Executed ", name, " => ", anyChange, "; ", cache.list);
      }
      // logln("::", anyChange, "; ", cache.list);
      if (!anyChange) break;
    }
    foreach (opt; newOpts)
      log("[", unique(opt), "]");
      
    string join(string[] s) {
      string res;
      foreach (str; s) { if (res) res ~= ", "; res ~= str; }
      return res;
    }
    if (newOpts && debugOpts) logln("Opt: ", goodOpts.join(), " + ", newOpts/+, " - ", unused.keys+/);
    if (newOpts) logln("Unused: ", unused.keys);
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
    code ~= Format(t, "\n");
  }
  void genAsm(void delegate(string) dg) {
    flush();
    foreach (name, data; globvars) {
      dg(Format(".comm\t", name, ",", data._0, "\n"));
      assert(!data._1, "4");
    }
    dg(".section\t.tbss,\"awT\",@nobits\n");
    foreach (name, size; uninit_tlsvars) {
      auto alignment = size;
      if (alignment > 16) alignment = 16;
      if (alignment == 12) alignment = 16; // TODO: powers-of-two properly
      dg("\t.globl "); dg(name); dg("\n");
      dg(Format("\t.align ", alignment, "\n\t.type ")); dg(name); dg(", @object\n");
      dg(Format("\t.size ", name, ", ", size, "\n"));
      dg("\t"); dg(name); dg(":\n");
      dg(Format("\t.zero ", size, "\n"));
    }
    dg(".section\t.tdata,\"awT\",@progbits\n");
    foreach (name, data; tlsvars) {
      auto alignment = data._0;
      if (alignment > 16) alignment = 16;
      dg("\t.globl "); dg(name); dg("\n");
      dg(Format("\t.align ", alignment, "\n\t.type ", name, ", @object\n"));
      dg(Format("\t.size ", name, ", ", data._0, "\n"));
      dg("\t"); dg(name); dg(":\n");
      assert(data._1);
      auto parts = data._1.split(",");
      assert(parts.length * nativePtrSize == data._0,
              Format("Length mismatch: ", parts.length, " * ", 
                    nativePtrSize, " != ", data._0, " for ", data._1));
      dg("\t.long ");
      foreach (i, part; parts) {
        if (i) dg(", ");
        dg(part);
      }
      dg("\n");
    }
    dg(".section\t.rodata\n");
    foreach (name, c; constants) {
      dg(name); dg(":\n");
      dg(".byte ");
      foreach (val; c) dg(Format(cast(ubyte) val, ", "));
      dg("0\n");
      dg(".global "); dg(name); dg("\n");
    }
    foreach (name, array; longstants) { // lol
      dg(name); dg(":\n");
      dg(".long ");
      foreach (val; array) dg(Format(val, ", "));
      dg("0\n");
      dg(".global "); dg(name); dg("\n");
    }
    dg(".text\n");
    dg(code);
  }
}
