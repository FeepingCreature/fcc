module asmfile;

import assemble, ast.types;

import tools.log, tools.functional: map;
import tools.base: between, slice, startsWith, atoi;
class AsmFile {
  int[string] globals;
  ubyte[][string] constants;
  string[][string] longstants; // sorry
  int[string] globvars, tlsvars;
  string code;
  bool optimize;
  this(bool optimize) { New(cache); this.optimize = optimize; }
  Transcache cache;
  int currentStackDepth;
  void pushStack(string expr, IType type) {
    currentStackDepth += type.size;
    Transaction t;
    t.kind = Transaction.Kind.Push;
    t.source = expr;
    t.type = type;
    cache ~= t;
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
  void call(string what) {
    Transaction t;
    t.kind = Transaction.Kind.Call;
    t.dest = what;
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
    res ~= `void `~name~`() {
      auto match = cache.findMatch("`~name~`", (Transaction[] list) {
        // logln("cond for `~name~`: ", list);
        if (list.length >= ` ~ ctToString(instrs);
    {
      string temp = stmt_match, merp; int i;
      while ((merp=temp.ctSlice(",")).length)
        res ~= ` && (` ~ merp.ctStrip().ctReplace("^", `list[` ~ ctToString(i++) ~ `].kind == Transaction.Kind.`) ~ `)`;
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
      } while (match.advance());
    }
    `~name~`();
    `;
    return res.ctReplace(
          "$SUBSTWITH", `foreach (ref $T res; onceThenCall(($T t) { match.replaceWith(t); })) with (res)`,
          "$SUBST", `match.replaceWith`,
          "$TK", `Transaction.Kind`,
          "$T", `Transaction`,
          "$RESET", `{ if (!match.reset()) break; goto _loophead; }`);
  }
  static bool isRegister(string s) {
    return s.length > 2 && s[0] == '%' && s[1] != '(';
  }
  static bool isLiteral(string s) {
    return s.length && s[0] == '$';
  }
  static int literalToInt(string s) {
    assert(isLiteral(s));
    return s[1 .. $].atoi();
  }
  void flush() {
    bool goodMovSize(int i) { return i == 4 || i == 2 || i == 1; }
    if (optimize) {
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
      mixin(opt("collapse_push_pop", `^Push, ^Pop: ($0.type.size == $1.type.size) && (!$0.source.isRelative() || !$1.dest.isRelative()) =>
        if ($0.source == $1.dest) { /*logln("Who the fuck produced this retarded bytecode: ", match[]);*/ $SUBST(null); continue; }
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
          logln(":: ", s);
          assert(false);
        }
        void doMov($TK kind, int sz) {
          while (size >= sz) {
            $T mv;
            mv.kind = $TK.Mov;
            mv.from = source; mv.to = dest;
            size -= sz;
            if (size) {
              mv.from.incr(sz);
              mv.to.incr(sz);
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
      mixin(opt("mov_and_math", `^Mov, ^MathOp: $0.to == $1.op1 && !isRelative($0.from) =>
        $SUBSTWITH {
          kind = $TK.MathOp;
          opName = $1.opName; op1 = $0.from; op2 = $1.op2;
        }
      `));
      mixin(opt("add_and_pop_reg", `^MathOp, ^Pop: $0.op2 == "(%esp)" && ($0.op1.find($1.to) == -1) =>
        $T res = $0;
        res.op2 = $1.to;
        $SUBST([$1, res]);
        $RESET;
      `));
      collapse_push_pop(); // rerun
      mixin(opt("literals_first", `^MathOp, ^MathOp: $0.op2 == $1.op2 && $0.op1.isRegister() && $1.op1.isLiteral() =>
        $SUBST([$1, $0]);
        $RESET;
      `));
      mixin(opt("fold_math", `^Mov, ^MathOp: $1.opName == "addl" && $0.to == $1.op2 && $0.from.isLiteral() && $1.op1.isLiteral() =>
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
      mixin(opt("make_call_direct", `^Mov, ^Call: $0.to == $1.dest => $SUBSTWITH { kind = $TK.Call; dest = $0.from; } `));
      mixin(opt("fold_mov_push", `^Mov, ^Push: $0.to == $1.source => $SUBSTWITH { kind = $TK.Push; type = $1.type; source = $0.from; }`));
      mixin(opt("fold_mov_pop",  `^Mov, ^Pop : $0.from == $1.dest && $1.to == "(%esp)" => $SUBSTWITH { kind = $TK.SFree; size = $1.type.size; assert(size == nativeIntSize); }`));
      collapse_push_pop(); // again!
    }
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
    foreach (name, size; globvars) {
      res ~= Format(".comm\t", name, ",", size, "\n");
    }
    res ~= ".section\t.tbss,\"awT\",@nobits\n";
    foreach (name, size; tlsvars) {
      res ~= Format("\t.globl ", name, "\n");
      res ~= Format("\t.align ", size, "\n\t.type ", name, ", @object\n\t.size ", name, ", ", size, "\n");
      res ~= Format("\t", name, ":\n\t.zero ", size, "\n");
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
