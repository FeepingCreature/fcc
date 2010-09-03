module optimizer;

import assemble, tools.base, ast.base, ast.types;
alias asmfile.startsWith startsWith;

struct onceThenCall {
  void delegate(Transaction) dg;
  int opApply(int delegate(ref Transaction) _body) {
    Transaction tr;
    _body(tr);
    dg(tr);
    return 0;
  }
}

string opt(string name, string s) {
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
  res ~= `bool `~name~`(Transcache cache, ref int[string] labels_refcount) {
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
  opts ~= stuple(&`~name~`, "`~name~`", true);
  /* `~name~`();*/
  `;
  return res.ctReplace(
        "$SUBSTWITH", `foreach (ref $T res; onceThenCall(($T t) { match.replaceWith(t); })) with (res)`,
        "$SUBST", `match.replaceWith`,
        "$TK", `Transaction.Kind`,
        "$T", `Transaction`);
}

bool isRegister(string s) {
  return s.length > 2 && s[0] == '%' && s[1] != '(';
}

bool isLiteral(string s) {
  return s.length && s[0] == '$';
}

bool isNumLiteral(string s) {
  if (!s.isLiteral()) return false;
  foreach (ch; s[1 .. $])
    if (ch != '-' && (ch < '0' || ch > '9')) return false;
  return true;
}

int literalToInt(string s) {
  assert(isLiteral(s), "1");
  return s[1 .. $].atoi();
}

bool referencesStack(ref Transaction t) {
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

bool changesESP(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ Pop);
}

bool hasSource(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ FloatLoad);
}

bool hasDest(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Pop /or/ Call /or/ FloatStore /or/ FloatPop);
}

bool hasFrom(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Mov /or/ Mov2 /or/ Mov1);
}
alias hasFrom hasTo;

bool hasSize(ref Transaction t) {
  with (Transaction.Kind)
    return !!(t.kind == Push /or/ Pop /or/ Mov /or/ Mov2 /or/ Mov1);
}

int size(ref Transaction t) {
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
Stuple!(bool delegate(Transcache, ref int[string]), string, bool)[] opts;
bool optsSetup;

void setupOpts() {
  if (optsSetup) return;
  optsSetup = true;
  bool goodMovSize(int i) { return i == 4 || i == 2 || i == 1; }
  // alloc/free can be shuffled down past _anything_ that doesn't reference stack.
  mixin(opt("sort_mem", `^SAlloc || ^SFree, *: !referencesStack($1) => $SUBST([$1, $0]); `));
  mixin(opt("sort_pointless_mem", `^SAlloc || ^SFree, *:
    (hasSource($1) || hasDest($1) || hasFrom($1) || hasTo($1)) && !changesESP($1)
    =>
    string* sp;
    $T t = $1.dup;
    bool used;
    void doStuff(ref string s) {
      if (s.between("(", ")") != "%esp") return;
      auto offs = s.between("", "(").atoi();
      if ($0.kind == $TK.SAlloc) {
        if (offs > $0.size) { // will be unaffected
          s = Format(offs - $0.size, "(%esp)");
          used =  true;
        }
      } else {
        s = Format(offs + $0.size, "(%esp)");
        used = true;
      }
    }
    if (hasSource($1)) doStuff(t.source);
    if (hasDest  ($1)) doStuff(t.dest);
    if (hasFrom  ($1)) doStuff(t.from);
    if (hasTo    ($1)) doStuff(t.to);
    if (used)
      $SUBST([t, $0]);
  `));
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
        mv.kind = kind;
        mv.from = source; mv.to = dest;
        mv.stackdepth = $0.stackdepth;
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
    a1.stackdepth = $0.stackdepth;
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
  mixin(opt("float_addition_is_commutative", `^FloatPop, ^FloatLoad, ^FloatLoad, ^FloatMath: $3.opName == "fadd" => auto t = $0; t.kind = $TK.FloatStore; $SUBST([t, $1, $3]); `));
  
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
    (  hasSource($0) && $0.source.between("(", ")") == "%ebp"
    || hasDest  ($0) && $0.dest  .between("(", ")") == "%ebp"
    || hasFrom  ($0) && $0.from  .between("(", ")") == "%ebp"
    )
    && $0.hasStackdepth && (!hasSize($0) || size($0) != 1)
    =>
    $T t = $0;
    void doStuff(ref string str) {
      auto offs = str.between("", "(").atoi(); 
      auto new_offs = offs + t.stackdepth;
      if (new_offs) str = Format(new_offs, "(%esp)");
      else str = "(%esp)";
      $SUBST([t]);
    }
    bool skip;
    if ($0.kind == $TK.Push /or/ $TK.Pop) {
      // if we can't do the push in one step
      if ($0.type.size != 4 /or/ 2 /or/ 1) 
        skip = true;
    }
    if (!skip) {
      if (hasSource(t) && t.source.between("(", ")") == "%ebp") doStuff(t.source);
      if (hasDest  (t) && t.dest  .between("(", ")") == "%ebp") doStuff(t.dest);
      if (hasFrom  (t) && t.from  .between("(", ")") == "%ebp") doStuff(t.from);
      if (hasTo    (t) && t.to    .between("(", ")") == "%ebp") doStuff(t.to);
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

// Stuple!(bool delegate(Transcache, ref int[string]), string, bool)[] opts;
// what's necessary to uniquely identify an opt
string unique(string s) {
  string res;
  int count() {
    int c;
    foreach (entry; opts)
      if (entry._1.startsWith(res)) c++;
    return c;
  }
  while (count > 1) {
    if (!s.length)
      return res; // give up
    res ~= s.take();
  }
  return res;
}
