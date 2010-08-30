module asmfile;

import assemble, ast.types, parseBase: startsWith;

import tools.log, tools.functional: map;
import tools.base: between, slice, atoi, split, stuple, apply, swap;
class AsmFile {
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
  this(bool optimize) { New(cache); this.optimize = optimize; }
  Transcache cache;
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
    if (!mayBeBigger && currentStackDepth < i)
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
    return Format("label", labelCounter++);
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
    foreach (t; cache.list) {
      if (t.kind != Transaction.Kind.Label) newlist ~= t;
      else foreach (name; t.names) if (name in labels_refcount && labels_refcount[name] > 0) { newlist ~= t; break; }
    }
    cache.list = newlist;
    labels_refcount = null;
  }
  int lastStackDepth;
  void comment(T...)(T t) {
    if (!optimize)
      put("# [", currentStackDepth, ": ", currentStackDepth - lastStackDepth, "]: ", t);
    lastStackDepth = currentStackDepth;
  }
  static struct onceThenCall {
    void delegate(Transaction) dg;
    int opApply(int delegate(ref Transaction) _body) {
      Transaction tr;
      _body(tr);
      dg(tr);
      return 0;
    }
  }
  static string opt(string name, string s) {
    string src = s.ctSlice("=>"), dest = s;
    string stmt_match = src.ctSlice(":");
    int instrs = 0;
    {
      string temp = stmt_match;
      while (temp.ctSlice(",").length) {
        src = src  .ctReplace("$"~ctToString(instrs), "match["~ctToString(instrs)~"]");
        dest = dest.ctReplace("$"~ctToString(instrs), "match["~ctToString(instrs)~"]");
        instrs ++;
      }
    }
    string res;
    res ~= `bool `~name~`(typeof(this) _that) { with (_that) {
        bool changed;
        auto match = cache.findMatch("`~name~`", (Transaction[] list) {
          // logln("cond for `~name~`: ", list);
          if (list.length >= ` ~ ctToString(instrs);
      {
        string temp = stmt_match, merp; int i;
        while ((merp=temp.ctSlice(",")).length) {
          if (merp.ctStrip() == "*") i++;
          else
            res ~= ` && (` ~ merp.ctStrip().ctReplace("^", `list[` ~ ctToString(i++) ~ `].kind == Transaction.Kind.`) ~ `)`;
        }
      }
      res ~= `) {
            return ` ~ ctToString(instrs) ~ `;
          }
          else return 0;
        });
        if (match.length) _loophead:do { `;
      if (src.ctStrip().length) res ~= `
          if (!(`~src~`)) continue;`;
      res ~= dest~`
          if (match.modded) changed = true;
        } while (match.advance());
        return changed;
      }
    }
    opts ~= stuple(this /apply/ &`~name~`, "`~name~`", true);
    /* `~name~`();*/
    `;
    return res.ctReplace(
          "$SUBSTWITH", `foreach (ref $T res; onceThenCall(($T t) { match.replaceWith(t); })) with (res)`,
          "$SUBST", `match.replaceWith`,
          "$TK", `Transaction.Kind`,
          "$T", `Transaction`);
  }
  static bool isRegister(string s) {
    return s.length > 2 && s[0] == '%' && s[1] != '(';
  }
  static bool isLiteral(string s) {
    return s.length && s[0] == '$';
  }
  static bool isNumLiteral(string s) {
    if (!s.isLiteral()) return false;
    foreach (ch; s[1 .. $])
      if (ch != '-' && (ch < '0' || ch > '9')) return false;
    return true;
  }
  static int literalToInt(string s) {
    assert(isLiteral(s), "1");
    return s[1 .. $].atoi();
  }
  static bool referencesStack(ref Transaction t) {
    bool foo(string s) { return s.find("%esp") != -1 || s.find("%ebp") != -1; }
    with (Transaction.Kind) switch (t.kind) {
      case   SAlloc, SFree, Pop, Push : return true;
      case                       Call : return true;
      case                        Mov : return t.from.foo() || t.to.foo();
      case                     MathOp : return t.op1.foo() || t.op2.foo();
      case                  FloatLoad : return t.source.foo();
      case       FloatPop, FloatStore : return t.dest.foo();
      case                  FloatMath : return false;
      default: break;
    }
    return true;
  }
  static bool hasSource(ref Transaction t) {
    with (Transaction.Kind)
      return !!(t.kind == Push /or/ FloatLoad);
  }
  static bool hasDest(ref Transaction t) {
    with (Transaction.Kind)
      return !!(t.kind == Pop /or/ Call /or/ FloatStore /or/ FloatPop);
  }
  static bool hasSize(ref Transaction t) {
    with (Transaction.Kind)
      return !!(t.kind == Push /or/ Pop /or/ Mov /or/ Mov2 /or/ Mov1);
  }
  static int size(ref Transaction t) {
    with (Transaction.Kind) switch (t.kind) {
      case Push: return t.type.size;
      case Pop: return t.type.size;
      case Mov: return 4;
      case Mov2: return 2;
      case Mov1: return 1;
    }
    assert(false);
  }
  // dg, name, allow
  Stuple!(bool delegate(), string, bool)[] opts;
  bool optsSetup;
  void setupOpts() {
    if (optsSetup) return;
    optsSetup = true;
    bool goodMovSize(int i) { return i == 4 || i == 2 || i == 1; }
    // alloc can be shuffled down past _anything_ that doesn't reference ESP.
    mixin(opt("sort_mem", `^SAlloc || ^SFree, *: !referencesStack($1) => $SUBST([$1, $0]); `));
    mixin(opt("collapse_alloc_frees", `^SAlloc || ^SFree, ^SAlloc || ^SFree =>
      int sum_inc;
      if ($0.kind == $TK.SAlloc) sum_inc += $0.size;
      else sum_inc -= $0.size;
      if ($1.kind == $TK.SAlloc) sum_inc += $1.size;
      else sum_inc -= $1.size;
      if (!sum_inc) $SUBST(null);
      else $SUBSTWITH {
        if (sum_inc > 0) kind = $TK.SAlloc;
        else kind = $TK.SFree;
        size = abs(sum_inc);
      }
    `));
    mixin(opt("collapse_alloc_free_nop", `^SAlloc || ^SFree => if (!$0.size) $SUBST(null); `));
    mixin(opt("collapse_push_pop", `^Push, ^Pop:
      ($0.type.size == $1.type.size) && (!$0.source.isMemRef() || !$1.dest.isMemRef())
      =>
      if ($0.source == $1.dest) { /+logln("Who the fuck produced this retarded bytecode: ", match[]);+/ $SUBST(null); continue; }
      $T[] movs;
      int size = $0.type.size;
      string source = $0.source, dest = $1.dest;
      void incr(ref string s, int sz) {
        if (s.length && !s.startsWith("$") && !s.startsWith("%") && !s.startsWith("(")) {
          // num(reg)
          auto num = s.slice("(").atoi();
          s = Format(num + sz, "(", s);
          return;
        }
        if (s.length && s[0] == '$') { // number; repeat
          return;
        }
        logln(":: ", s, "; ", $0.source, " -> ", $1.dest);
        assert(false, "2");
      }
      void doMov($TK kind, int sz) {
        while (size >= sz) {
          $T mv;
          mv.kind = $TK.Mov;
          mv.from = source; mv.to = dest;
          size -= sz;
          if (size) {
            source.incr(sz);
            dest.incr(sz);
          }
          movs ~= mv;
        }
      }
      doMov($TK.Mov, 4);
      doMov($TK.Mov2, 2);
      doMov($TK.Mov1, 1);
      $SUBST(movs);
    `));
    mixin(opt("add_mov", `^MathOp, ^Mov: $0.opName == "addl" && $0.op2 == "%eax" && $0.op2 == $1.from && $0.op1 == $1.to =>
      $SUBSTWITH {
        kind = $TK.MathOp;
        opName = $0.opName; op1 = "%eax"; op2 = $0.op1;
      }
    `));
    mixin(opt("fold_add_sub", `^MathOp, ^MathOp:
      $0.op2 == $1.op2 && $0.op1.isNumLiteral() && $1.op1.isNumLiteral()
      && $0.opName == "subl" && $1.opName == "addl"
      =>
      $SUBSTWITH {
        kind = $TK.MathOp;
        opName = "addl";
        op1 = Format("$", - $0.op1.literalToInt() + $1.op1.literalToInt());
        op2 = $0.op2;
      }
    `));
    mixin(opt("mov_and_math", `^Mov, ^MathOp: $0.to == $1.op1 && !isRelative($0.from) =>
      $SUBSTWITH {
        kind = $TK.MathOp;
        opName = $1.opName; op1 = $0.from; op2 = $1.op2;
      }
    `));
    mixin(opt("add_and_pop_reg", `^MathOp, ^Pop: $0.op2 == "(%esp)" && ($0.op1.find($1.to) == -1) =>
      auto res = $0.dup;
      res.op2 = $1.to;
      $SUBST([$1, res]);
    `));
    mixin(opt("literals_first", `^MathOp, ^MathOp: $0.op2 == $1.op2 && $0.op1.isRegister() && $1.op1.isLiteral() =>
      $SUBST([$1, $0]);
    `));
    mixin(opt("fold_math", `^Mov, ^MathOp: $1.opName == "addl" && $0.to == $1.op2 && $0.from.isNumLiteral() && $1.op1.isNumLiteral() =>
      $SUBSTWITH {
        kind = $TK.Mov;
        from = Format("$", $0.from.literalToInt() + $1.op1.literalToInt());
        to = $0.to;
      }
    `));
    mixin(opt("fold_math_push_add", `^Push, ^MathOp: $0.source.isLiteral() && $1.op1.isLiteral() && $1.op2 == "(%esp)" =>
      $SUBSTWITH {
        res = $0;
        int i1 = $0.source.literalToInt(), i2 = $1.op1.literalToInt();
        switch ($1.opName) {
          case "addl": source = Format("$", i1+i2); break;
          case "subl": source = Format("$", i1-i2); break;
          case "imull": source = Format("$", i1*i2); break;
          default: assert(false, "Unsupported op: "~$1.opName);
        }
      }
    `));
    mixin(opt("fold_mul", `^Push, ^Mov, ^MathOp, ^Mov:
      $0.source.isLiteral() && $0.type.size == 4 &&
      $1.from.isLiteral() && $1.to == $2.op2 &&
      $2.op1 == "(%esp)" && $2.op2 == $3.from && $2.opName == "imull" &&
      $3.to == "(%esp)"
      =>
      $SUBSTWITH {
        res = $0;
        auto i1 = $0.source.literalToInt(), i2 = $1.from.literalToInt();
        source = Format("$", i1*i2);
      }
    `));
    /// location access to a struct can be translated into an offset instruction
    mixin(opt("indirect_access", `^Mov, ^MathOp, ^Pop:
      $0.from.isLiteral() && $1.opName == "addl" && $1.op1.isRegister() &&
      $0.to == $1.op2 && $0.to == "%eax" && $2.dest == "(%eax)"
      =>
      $SUBSTWITH {
        kind = $TK.Pop;
        type = $2.type;
        dest = Format($0.from.literalToInt(), "(", $1.op1, ")");
      }
    `));
    mixin(opt("add_into_pop", `^MathOp, ^Pop:
      $0.opName == "addl" && $0.op1 == $1.dest &&
      $0.op2 == "(%esp)" && $1.type.size == 4
      =>
      $T t1 = $0, t2;
      swap(t1.op1, t1.op2);
      t2.kind = $TK.SFree;
      t2.size = 4;
      $SUBST([t1, t2]);
    `));
    mixin(opt("indirect_access_push", `^Mov, ^MathOp, ^Push || ^FloatLoad:
      $0.from.isLiteral() && $1.opName == "addl" && $1.op1.isRegister() &&
      $0.to == $1.op2 && $0.to == "%eax" && $2.source == "(%eax)"
      =>
      $SUBSTWITH {
        kind = $2.kind;
        type = $2.type;
        source = Format($0.from.literalToInt(), "(", $1.op1, ")");
      }
    `));
    mixin(opt("indirect_access_sub_fload", `^MathOp, ^FloatLoad:
      $0.opName == "subl" && $0.op1.isLiteral() && $0.op2 == "%eax"
      && $1.source.between("(", ")") == "%eax"
      =>
      $SUBSTWITH {
        kind = $1.kind;
        source = Format($1.source.between("", "(").atoi() - $0.op1.literalToInt(), "(%eax)");
      }
    `));
    mixin(opt("merge_literal_adds", `^MathOp, ^MathOp:
      $0.opName == "addl" && $1.opName == "addl" &&
      $0.op1.isLiteral() && $1.op1.isLiteral() &&
      $0.op2 == "%eax" && $1.op2 == "%eax"
      =>
      $SUBSTWITH {
        kind = $TK.MathOp;
        opName = "addl";
        op1 = Format("$", $0.op1.literalToInt() + $1.op1.literalToInt());
        op2 = "%eax";
      }
    `));
    mixin(opt("fold_rel_access", `^Mov, ^MathOp, ^Mov:
      $0.from.isLiteral() &&
      $1.opName == "addl" && $1.op1.isRegister() && $1.op2 == $0.to &&
      $2.from.isRelative()
      =>
      $SUBSTWITH {
        res = $2;
        auto i1 = $0.from.literalToInt(), i2 = $2.from.slice("(").atoi();
        from = Format(i1 + i2, "(", $1.op1, ")");
      }
    `));
    // cleanup
    mixin(opt("alloc_move_to_push", `^SAlloc, ^Mov:
      $0.size == 4 && $1.to == "(%esp)"
      =>
      $SUBSTWITH {
        kind = $TK.Push;
        type = Single!(SysInt);
        source = $1.from;
      }
    `));
    mixin(opt("load_from_push", `^Push, ^FloatLoad:
      !$0.source.isRegister() && $1.source == "(%esp)"
      =>
      $T a1 = $1.dup, a2;
      a1.source = $0.source;
      if ($1.hasStackdepth) a1.stackdepth = $1.stackdepth - 4;
      a2.kind = $TK.SAlloc;
      a2.size = 4;
      $SUBST([a1, a2]);
    `));
    mixin(opt("fold_fpop_and_pop", `^FloatPop, ^Pop:
      $0.dest == "(%esp)" && $1.type.size == 4
      =>
      $T a1, a2;
      a1.kind = $TK.FloatPop;
      a1.dest = $1.dest;
      a2.kind = $TK.SFree;
      a2.size = 4;
      $SUBST([a1, a2]);
    `));
    
    mixin(opt("fold_float_pop_load", `^FloatPop, ^FloatLoad, ^SFree: $0.dest == $1.source && $0.dest == "(%esp)" && $2.size == 4 => $SUBST([$2]);`));
    mixin(opt("fold_float_alloc_load_store", `^SAlloc, ^FloatLoad, ^FloatPop: $0.size == 4 && $2.dest == "(%esp)" => $SUBSTWITH { kind = $TK.Push; source = $1.source; type = Single!(Float); }`));
    mixin(opt("fold_float_pop_load_to_store", `^FloatPop, ^FloatLoad: $0.dest == $1.source => $SUBSTWITH { kind = $TK.FloatStore; dest = $0.dest; }`));
    mixin(opt("make_call_direct", `^Mov, ^Call: $0.to == $1.dest => $SUBSTWITH { kind = $TK.Call; dest = $0.from; } `));
    mixin(opt("fold_mov_push", `^Mov, ^Push: $0.to == $1.source => $T t; with (t) { kind = $TK.Push; type = $1.type; source = $0.from; } $SUBST([t, $0]); `));
    mixin(opt("fold_mov_pop",  `^Mov, ^Pop : $0.from == $1.dest && $0.to == "(%esp)"
      =>
      $SUBSTWITH {
        kind = $TK.SFree;
        size = $1.type.size;
        assert(size == nativeIntSize, "3");
      }
    `));
    // some very special cases
    mixin(opt("float_meh",  `^SFree, ^FloatSwap, ^SAlloc: $0.size == $2.size => $SUBST([$1]); `));
    mixin(opt("float_meh_2",  `^FloatStore, ^FloatMath, ^FloatStore || ^FloatPop: $0.dest == $2.dest => $SUBST([$1, $2]); `));
    mixin(opt("float_meh_3",  `^FloatStore, ^FloatLoad, ^FloatMath, ^FloatStore: $0.dest != $1.source && $0.dest == $3.dest => $SUBST([$1, $2, $3]); `));
    mixin(opt("float_pointless_swap",  `^FloatSwap, ^FloatMath: $1.opName == "fadd" || $1.opName == "fmul" => $SUBST([$1]); `));
    mixin(opt("float_pointless_store",  `^FloatStore, ^FloatPop: $0.dest == $1.dest => $SUBST([$1]); `));
    
    // typical for delegates
    mixin(opt("member_access_1", `^Push, ^Push, ^Mov, ^SFree, ^Push:
      $0.type.size /and/ $1.type.size /and/ $4.type.size == 4 && $2.from == "4(%esp)" && $3.size == 8 && $2.to == $4.source
      =>
      $SUBST([$0]);
    `));
    mixin(opt("member_access_2", `^Push, ^Push, ^Mov, ^SFree, ^Call:
      $0.type.size /and/ $1.type.size == 4 && $2.from == "0(%esp)" && $3.size == 8 && $2.to == $4.dest
      =>
      $SUBSTWITH {
        kind = $TK.Call;
        dest = $1.source;
      }
    `));
    mixin(opt("indirect_access_2", `^Mov, ^MathOp, *:
      (hasDest($2) || hasSource($2)) &&
      $0.from.isRegister() && $1.opName == "addl" && $1.op1.isLiteral() &&
      $0.to == $1.op2 && $0.to == "%eax" && (hasDest($2) && $2.dest == "(%eax)" || hasSource($2) && $2.source == "(%eax)")
      =>
      $T t = $2;
      if (hasDest($2))
        t.dest  = Format($1.op1.literalToInt(), "(", $0.from, ")");
      else
        t.source = Format($1.op1.literalToInt(), "(", $0.from, ")");
      $SUBST([t]);
    `));
    mixin(opt("indirect_access_3", `^MathOp, *:
      hasSource($1) && $1.source == "(" ~ $0.op2 ~ ")" && $0.op1.isNumLiteral()
      =>
      auto t = $1;
      t.source = Format($0.op1.literalToInt(), $1.source);
      $SUBST([t]);
    `));
    mixin(opt("store_float_direct", `^FloatPop, ^Pop:
      $0.dest == "(%esp)" && $1.type.size == 4
      =>
      $T t1 = $0, t2;
      t1.dest = $1.dest;
      t2.kind = $TK.SFree;
      t2.size = 4;
      $SUBST([t1, t2]);
    `));
    mixin(opt("ebp_to_esp", `*:
      hasSource($0) && $0.source.between("(", ")") == "%ebp" && $0.hasStackdepth && (!hasSize($0) || size($0) != 1)
      =>
      auto offs = $0.source.between("", "(").atoi();
      auto new_offs = offs + $0.stackdepth;
      bool skip;
      if ($0.kind == $TK.Push) {
        // if we can't do the push in one step
        if ($0.type.size != 4 /or/ 2 /or/ 1) 
          skip = true;
      }
      if (!skip) $SUBSTWITH {
        res = $0.dup;
        source = Format(new_offs, "(%esp)");
      }
    `));
    
    // jump opts
    mixin(opt("join_labels", `^Label, ^Label => auto t = $0; t.names = t.names ~ $1.names; $SUBST([t]); `));
    mixin(opt("pointless_jump", `^Jump, ^Label:
      $1.hasLabel($0.dest)
      =>
      labels_refcount[$0.dest] --;
      $SUBST([$1]);
    `));
  }
  string[] goodOpts;
  void runOpts() {
    setupOpts;
    string optstr;
    bool[string] unused;
    bool delegate()[string] map;
    foreach (entry; opts) if (entry._2) {
      unused[entry._1] = true;
      map[entry._1] = entry._0;
    }
    foreach (opt; goodOpts) {
      unused.remove(opt);
      map[opt]();
    }
    while (true) {
      bool anyChange;
      foreach (entry; opts) if (entry._2) {
        auto opt = entry._0, name = entry._1;
        if (opt()) {
          unused.remove(name);
          
          if (optstr.length) optstr ~= ", ";
          optstr ~= name;
          
          goodOpts ~= name;
          anyChange = true;
        }
        // logln("Executed ", name, " => ", anyChange, "; ", cache.list);
      }
      // logln("::", anyChange, "; ", cache.list);
      if (!anyChange) break;
      // logln("optstr now ", optstr, ", omitted: ", unused.keys);
    }
    
    string join(string[] s) {
      string res;
      foreach (str; s) { if (res) res ~= ", "; res ~= str; }
      return res;
    }
    if (optstr && debugOpts) logln("Opt: ", goodOpts.join(), " + ", optstr, " - ", unused.keys);
  }
  void flush() {
    if (optimize) runOpts;
    foreach (entry; cache.list) if (auto line = entry.toAsm()) _put(line);
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
    foreach (name, data; globvars) {
      res ~= Format(".comm\t", name, ",", data._0, "\n");
      assert(!data._1, "4");
    }
    res ~= ".section\t.tbss,\"awT\",@nobits\n";
    foreach (name, size; uninit_tlsvars) {
      res ~= Format("\t.globl ", name, "\n");
      res ~= Format("\t.align ", size, "\n\t.type ", name, ", @object\n");
      res ~= Format("\t.size ", name, ", ", size, "\n");
      res ~= Format("\t", name, ":\n");
      res ~= Format("\t.zero ", size, "\n");
    }
    res ~= ".section\t.tdata,\"awT\",@progbits\n";
    foreach (name, data; tlsvars) {
      res ~= Format("\t.globl ", name, "\n");
      res ~= Format("\t.align ", data._0, "\n\t.type ", name, ", @object\n");
      res ~= Format("\t.size ", name, ", ", data._0, "\n");
      res ~= Format("\t", name, ":\n");
      assert(data._1);
      auto parts = data._1.split(",");
      assert(parts.length * nativePtrSize == data._0,
              Format("Length mismatch: ", parts.length, " * ", 
                    nativePtrSize, " != ", data._0, " for ", data._1));
      res ~= "\t.long ";
      foreach (i, part; parts) {
        if (i) res ~= ", ";
        res ~= part;
      }
      res ~= "\n";
    }
    res ~= ".section\t.rodata\n";
    foreach (name, c; constants) {
      res ~= Format(name, ":\n");
      res ~= ".byte ";
      foreach (val; c) res ~= Format(cast(ubyte) val, ", ");
      res ~= "0\n";
    }
    foreach (name, array; longstants) { // lol
      res ~= Format(name, ":\n");
      res ~= ".long ";
      foreach (val; array) res ~= Format(val, ", ");
      res ~= "0\n";
    }
    res ~= ".text\n";
    res ~= code;
    return res;
  }
}
