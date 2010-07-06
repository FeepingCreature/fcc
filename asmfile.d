module asmfile;

import assemble, ast.types, ast.base;

import tools.log, tools.functional: map;
import tools.base: between, slice, startsWith;
class AsmFile {
  ubyte[][string] constants;
  string code;
  bool optimize;
  this(bool optimize) { New(cache); this.optimize = optimize; }
  Transcache cache;
  int currentStackDepth;
  void pushStack(string expr, IType type) {
    currentStackDepth += type.size;
    if (type.size == 1) currentStackDepth ++;
    Transaction t;
    t.kind = Transaction.Kind.Push;
    t.source = expr;
    t.type = type;
    cache ~= t;
  }
  void popStack(string dest, IType type) {
    currentStackDepth -= type.size;
    if (type.size == 1) currentStackDepth --;
    Transaction t;
    t.kind = Transaction.Kind.Pop;
    t.dest = dest;
    t.type = type;
    cache ~= t;
  }
  int checkptStack() {
    return currentStackDepth;
  }
  void restoreCheckptStack(int i) {
    if (currentStackDepth < i)
      throw new Exception("Tried to unwind stack while unwound further - logic error");
    sfree(currentStackDepth - i);
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
  void jump(string label) {
    put("jmp ", label);
  }
  import tools.ctfe;
  void jumpOn(bool smaller, bool equal, bool greater, string label) {
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
  void mathOp(string which, string op1, string op2) {
    Transaction t;
    t.kind = Transaction.Kind.MathOp;
    t.opName = which;
    t.op1 = op1; t.op2 = op2;
    cache ~= t;
  }
  int labelCounter; // Limited to 2^31 labels, le omg.
  string genLabel() {
    return Format("label", labelCounter++);
  }
  void emitLabel(string name) {
    put(name, ":");
  }
  int lastStackDepth;
  void comment(T...)(T t) {
    if (!optimize) put("# [", currentStackDepth - lastStackDepth, "]: ", t);
    lastStackDepth = currentStackDepth;
  }
  // opts
  void collapseAllocFrees() {
    auto match = cache.findMatch("collapseAllocFrees", (Transaction[] list) {
      auto match = Transaction.Kind.SAlloc /or/ Transaction.Kind.SFree;
      if (list.length >= 2 && list[0].kind == match && list[1].kind == match)
        return 2;
      else return cast(int) false;
    });
    if (!match.length) return;
    do {
      int sum_inc;
      auto l1 = match[0], l2 = match[1];
      if (l1.kind == Transaction.Kind.SAlloc) sum_inc += l1.size;
      else sum_inc -= l1.size;
      if (l2.kind == Transaction.Kind.SAlloc) sum_inc += l2.size;
      else sum_inc -= l2.size;
      if (!sum_inc) match.replaceWith(null);
      else {
        Transaction res;
        if (sum_inc > 0) res.kind = Transaction.Kind.SAlloc;
        else res.kind = Transaction.Kind.SFree;
        res.size = abs(sum_inc);
        match.replaceWith(res);
      }
    } while (match.advance());
  }
  // Using stack as scratchpad is silly and pointless
  void collapseScratchMove() {
    auto match = cache.findMatch("collapseScratchMove", (Transaction[] list) {
      if (list.length > 2 && list[0].kind /and/ list[1].kind == Transaction.Kind.Mov && (
        (list[0].to == "(%esp)" && list[1].from == "(%esp)" && list[2].kind == Transaction.Kind.SFree) ||
        (!list[0].to.isRelative() && list[0].to == list[1].from) // second mode .. remember, moves are MOVEs, not COPYs
      )) {
        return 2;
      }
      else return cast(int) false;
    });
    if (!match.length) return;
    do {
      // what the fuck
      if (match[0].from == match[1].to) {
        match.replaceWith(null);
        continue;
      }
      // logln("Collapse ", match[0], " into ", match[1]);
      Transaction res;
      res.kind = Transaction.Kind.Mov;
      res.from = match[0].from; res.to = match[1].to;
      if (!match[0].to.isRelative())
        res.usableScratch = match[0].to;
      match.replaceWith(res);
    } while (match.advance());
  }
  // same
  void collapseScratchPush() {
    auto match = cache.findMatch("collapseScratchPush", (Transaction[] list) {
      if (list.length >= 2 &&
          list[0].kind == Transaction.Kind.Push &&
          list[1].kind == Transaction.Kind.Pop &&
          (
            !list[0].source.isRelative()
            ||
            !list[1].dest.isRelative()
          )
        )
      {
        return 2;
      }
      else return cast(int) false;
    });
    if (!match.length) return;
    do {
      // what the fuck
      if (match[0].source == match[1].dest) {
        logln("Who the fuck produced this retarded bytecode: ", cache.list);
        match.replaceWith(null);
        continue;
      }
      // logln("Collapse ", match[0], " into ", match[1]);
      Transaction res;
      res.kind = Transaction.Kind.Mov;
      res.from = match[0].source; res.to = match[1].dest;
      match.replaceWith(res);
    } while (match.advance());
  }
  void collapseCompares() {
    auto match = cache.findMatch("collapseCompares", (Transaction[] list) {
      if (list.length >= 2 &&
          list[0].kind == Transaction.Kind.Mov &&
          list[1].kind == Transaction.Kind.Compare &&
          (
            list[1].op1 != list[0].to
            ||
            !list[0].from.isRelative()
          ) &&
          (list[1].op1 /or/ list[1].op2 == list[0].to)
      ) {
        return 2;
      }
      else return cast(int) false;
    });
    if (!match.length) return;
    do {
      Transaction res = match[1];
      if (match[1].op1 == match[0].to) res.op1 = match[0].from;
      else res.op1 = match[1].op1;
      if (match[1].op2 == match[0].to) res.op2 = match[0].from;
      else res.op2 = match[1].op2;
      match.replaceWith(res);
    } while (match.advance());
  }
  // add esp, move, sub esp; or reverse
  void collapsePointlessRegMove() {
    auto match = cache.findMatch("collapsePointlessRegMove", (Transaction[] list) {
      if (list.length < 3) return 0;
      if ( list[0].kind == Transaction.Kind.SFree
        && list[1].kind == Transaction.Kind.Mov && list[1].to == "(%esp)"
        && list[2].kind == Transaction.Kind.SAlloc && list[2].size == list[0].size)
      {
        return 3;
      }
      else return 0;
    });
    if (!match.length) return;
    do {
      Transaction res;
      res.kind = Transaction.Kind.Mov;
      res.from = match[1].from;
      res.usableScratch = match[1].usableScratch;
      res.to = Format(match[0].size, "(%esp)");
      match.replaceWith(res);
    } while (match.advance());
  }
  void binOpMathSpeedup() {
    auto match = cache.findMatch("binOpMathSpeedup", (Transaction[] list) {
      if (list.length < 3) return 0;
      if ( list[0].kind == Transaction.Kind.Mov && list[0].to == "(%esp)"
        && list[1].kind == Transaction.Kind.Mov && !dependsOnEsp(list[1]) && list[1].to != list[0].from
        && list[2].kind == Transaction.Kind.MathOp && list[2].op1 == "(%esp)")
      {
        return 3;
      }
      else return 0;
    });
    if (match.length) do {
      auto subst = match[2];
      subst.op1 = match[0].from;
      match.replaceWith([match[1], subst]);
    } while (match.advance);
    
    auto match2 = cache.findMatch("binOpMathSpeedup2", (Transaction[] list) {
      if (list.length < 3) return 0;
      if (list[0].kind == Transaction.Kind.Push && list[0].type.size == 4 &&
          list[1].kind == Transaction.Kind.MathOp && list[1].op1 == "(%esp)")
      {
        return 3;
      } else return 0;
    });
    if (match2.length) do {
      auto temp = match2[1];
      temp.op1 = match2[0].source;
      if (match2[2].kind == Transaction.Kind.SFree && match2[2].size == 4) {
        match2.replaceWith(temp);
      } else {
        if (match2[2].kind == Transaction.Kind.Mov && !dependsOnEsp(match2[2].from) && match2[2].to == "(%esp)") {
          Transaction npush;
          npush.kind = Transaction.Kind.Push;
          npush.source = match2[2].from;
          npush.type = Single!(SizeT);
          match2.replaceWith([temp, npush]);
        }/* else {
          match2.replaceWith([temp, match2[0], match2[2]]);
        }*/
      }
    } while (match2.advance);
  }
  static bool dependsOnEsp(string s) {
    return s.find("%esp") != -1;
  }
  static bool dependsOnEsp(Transaction t) {
    if (t.kind == Transaction.Kind.Mov)
      return dependsOnEsp(t.from) || dependsOnEsp(t.to);
    if (t.kind == Transaction.Kind.Push)
      return dependsOnEsp(t.source);
    if (t.kind == Transaction.Kind.Pop)
      return dependsOnEsp(t.dest);
    assert(false, Format("Cannot determine %esp dependency of ", t, ": unknown type of operation"));
  }
  static bool related(string reg1, string reg2) {
    if (auto b = reg1.between("(", ")")) reg1 = b;
    if (auto b = reg2.between("(", ")")) reg2 = b;
    return reg1 == reg2;
  }
  void sortByEspDependency() {
    auto match = cache.findMatch("sortByEspDependency", (Transaction[] list) {
      auto match = Transaction.Kind.Mov;
      if (list.length < 2) return 0;
      if (
          (
            list[0].kind == Transaction.Kind.SFree /or/ Transaction.Kind.SAlloc
            ||
            list[0].kind == Transaction.Kind.Push /or/ Transaction.Kind.Pop
              && !dependsOnEsp(list[0])
              && !related((list[0].kind == Transaction.Kind.Push)?list[0].source:list[0].dest, list[1].to)
          )
          && list[1].kind == Transaction.Kind.Mov && !dependsOnEsp(list[1])
        )
      {
        return 2;
      } else return 0;
    });
    if (match.length) do {
      match.replaceWith([match[1], match[0]]);
    } while (match.advance());
  }
  void removeRedundantPop() {
    auto match = cache.findMatch("removeRedundantPop", (Transaction[] list) {
      if (list.length < 2) return 0;
      // movl [FOO], (%esp)
      // popl [FOO]
      if (
          list[0].kind == Transaction.Kind.Mov && list[0].to == "(%esp)" &&
          list[1].kind == Transaction.Kind.Pop && list[1].dest == list[0].from
        )
      {
        return 2;
      } else return 0;
    });
    if (match.length) do {
      Transaction res;
      res.kind = Transaction.Kind.SFree;
      res.size = nativePtrSize;
      match.replaceWith(res);
    } while (match.advance());
  }
  void removeRedundantPushPop() {
    auto match = cache.findMatch("removeRedundantPushPop", (Transaction[] list) {
      if (list.length < 2) return 0;
      if (
          list[0].kind == Transaction.Kind.Push &&
          list[1].kind == Transaction.Kind.Pop &&
          list[1].type.size() == list[0].type.size() /and/ 4
        )
      {
        return 2;
      } else return 0;
    });
    if (match.length) do {
      Transaction res;
      res.kind = Transaction.Kind.Mov;
      res.from = match[0].source;
      res.to = match[1].dest;
      match.replaceWith(res);
    } while (match.advance());
  }
  void removePointlessPushFree() {
    auto match = cache.findMatch("removePointlessPushFree", (Transaction[] list) {
      if (list.length < 2) return 0;
      if (
          list[0].kind == Transaction.Kind.Push &&
          list[1].kind == Transaction.Kind.SFree &&
          list[1].size == list[0].type.size()
        )
      {
        return 2;
      } else return 0;
    });
    if (match.length) do {
      match.replaceWith(null);
    } while (match.advance());
  }
  void removePointlessPushMov() {
    auto match = cache.findMatch("removePointlessPushFree", (Transaction[] list) {
      if (list.length < 2) return 0;
      if (
          list[0].kind == Transaction.Kind.Push &&
          list[1].kind == Transaction.Kind.Mov &&
          list[0].type.size() == 4 &&
          list[1].from == "(%esp)" && list[1].to == list[0].source
        )
      {
        return 2;
      } else return 0;
    });
    if (match.length) do {
      match.replaceWith(match[0]);
    } while (match.advance());
  }
  static bool isIndirect(string addr) {
    return addr.find("(") != -1;
  }
  static bool isNum(string n) {
    return !!n.startsWith("$");
  }
  void MathToIndirectAddressing() {
    auto match = cache.findMatch("MathToIndirectAddressing", (Transaction[] list) {
      if (list.length < 3) return 0;
      // movl [FOO], [REG]
      // addl [VAL], [REG]
      // popl ([REG])
      // ->
      // popl [VAL]([FOO])
      if (list[0].kind == Transaction.Kind.Mov && !isIndirect(list[0].from) &&
          list[1].kind == Transaction.Kind.MathOp && list[1].opName == "addl" && isNum(list[1].op1) && list[1].op2 == list[0].to &&
          (
            list[2].kind == Transaction.Kind.Pop && list[2].dest == "("~list[0].to~")"
            ||
            list[2].kind == Transaction.Kind.Push && list[2].source == "("~list[0].to~")"
          )
        )
      {
        return 3;
      } else return 0;
    });
    if (match.length) do {
      Transaction res;
      res.kind = match[2].kind;
      res.type = match[2].type;
      auto op = match[1].op1;
      op.slice("$");
      op ~= "("~match[0].from~")";
      if (res.kind == Transaction.Kind.Pop)
        res.dest = op;
      else
        res.source = op;
      
      match.replaceWith(res);
    } while (match.advance());
  }
  void flush() {
    if (optimize) {
      collapseAllocFrees;
      collapseScratchMove;
      collapseScratchPush;
      collapsePointlessRegMove;
      collapseCompares;
      sortByEspDependency;
      collapseAllocFrees; // rerun
      removeRedundantPop;
      removeRedundantPushPop;
      binOpMathSpeedup;
      MathToIndirectAddressing;
      collapseScratchPush; // rerun
      removePointlessPushFree;
      removePointlessPushMov;
    }
    foreach (t; cache.list) {
      if (auto line = t.toAsm())
          _put(line);
    }
    cache.list = null;
  }
  void put(T...)(T t) {
    flush();
    _put(t);
  }
  void _put(T...)(T t) {
    code ~= Format(t, "\n");
  }
  string genAsm() {
    flush();
    string res;
    res ~= ".data\n";
    foreach (name, c; constants) {
      res ~= Format(name, ":\n");
      res ~= ".byte ";
      foreach (val; c) res ~= Format(cast(ubyte) val, ", ");
      res ~= "0\n";
    }
    res ~= ".text\n";
    res ~= code;
    return res;
  }
}
