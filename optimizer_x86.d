module optimizer_x86;

import tools.threads, tools.base, ast.base, tools.base;
import optimizer_base;
alias asmfile.startsWith startsWith;

// reference form
string cleanup(string s) {
  if (auto rest = s.startsWith("0(")) return "("~rest;
  return s;
}

bool collide(string a, string b) {
  if (auto ia = a.isIndirect()) a = ia;
  if (auto ib = b.isIndirect()) b = ib;
  return (a == b);
}

bool isCommutative(string op) {
  return op == "addl"  || op == "imull" || op == "xorl"
      || op == "fadd" || op == "fmul";
}

bool isMemRef(string s) {
  if (s.find("(") != -1) return true;
  if (s.startsWith("$")) return false;
  if (s.isUtilityRegister() || s == "%ebp") return false;
  if (s.startsWith("%gs:")) return true;
  return true;
}

bool isMemAccess(string s) {
  if (isMemRef(s)) return true;
  if (s.startsWith("$")) return !s.isNumLiteral();
  return false;
}

bool hasUtilityRegister(string reg) {
  if (reg.find("%eax") != -1 || reg.find("%ebx") != -1 || reg.find("%ecx") != -1 || reg.find("%edx") != -1)
    return true;
  return false;
}

bool isSSERegister(string reg) {
  return !!reg.startsWith("%xmm");
}

bool isSSEMathOp(string op) {
  return !!(op == "addps" /or/ "subps" /or/ "mulps" /or/ "divps");
}

struct OrderedFastHashlike(K, V, FastKeys...) {
  const FastEntries = 8;
  Stuple!(K, V)[FastEntries] fast;
  int fastlength;
  Stuple!(K, V)[] array;
  void clear() {
    fastlength = 0; array = null;
  }
  V* opIn_r(K k) {
    foreach (ref entry; fast[0..fastlength])
      if (entry._0 == k) return &entry._1;
    foreach (ref entry; array)
      if (entry._0 == k) return &entry._1;
    return null;
  }
  string toString() { return Format(fast[0..fastlength] ~ array); }
  V opIndex(K k) {
    if (auto p = opIn_r(k)) return *p;
    logln("No such key: ", k, ", in ", this);
    fail;
  }
  void opIndexAssign(V v, K k) {
    if (auto p = opIn_r(k)) { *p = v; return; }
    if (fastlength < FastEntries) {
      fast[fastlength++] = stuple(k, v);
      return;
    }
    array ~= stuple(k, v);
  }
  int length() { return fastlength + array.length; }
  int opApply(int delegate(ref K, ref V) dg) {
    foreach (entry; fast[0..fastlength])
      if (auto res = dg(entry._0, entry._1)) return res;
    foreach (entry; array)
      if (auto res = dg(entry._0, entry._1)) return res;
    return 0;
  }
  int find_in_array(K k) {
    foreach (i, e; array) if (e._0 == k) return i;
    return -1;
  }
  void remove(K k) {
    outer:while (true) {
      foreach (i, entry; fast[0..fastlength]) {
        if (entry._0 == k) {
          // shift the rest up
          for (int l = i+1; l < fastlength; ++l) {
            fast[l-1] = fast[l];
          }
          fastlength --;
          continue outer;
        }
      }
      break;
    }
    scope(success) { // reshuffle array into fast
      while (fastlength < FastEntries && array.length) {
        fast[fastlength++] = array[0];
        array = array[1..$];
      }
    }
    while (true) {
      auto pos = find_in_array(k);
      if (pos == -1) return;
      array = array[0 .. pos] ~ array[pos+1 .. $];
    }
  }
}

extern(C) long atoll(char *c);
alias atoll atoll_c;
long atoll(string s) { return atoll_c(toStringz(s)); }

struct SmartHashmap(V, K, FastKeys...) {
  V[K] hash;
  static assert(is(V == bool)); // only true is permitted (false == removed)
  const TupLength = FastKeys.length;
  bool[TupLength] fastkeys;
  void clear() {
    hash = null;
    foreach (i, key; FastKeys) fastkeys[i] = false;
  }
  K[] keys() {
    auto res = hash.keys;
    foreach (i, key; FastKeys)
      if (fastkeys[i]) res ~= key;
    return res;
  }
  V* opIn_r(K k) {
    foreach (i, key; FastKeys) {
      if (k == key) { if (fastkeys[i]) return &fastkeys[i]; else return null; }
    }
    return k in hash;
  }
  void remove(K k) {
    foreach (i, key; FastKeys) {
      if (k == key) { fastkeys[i] = false; return; }
    }
    hash.remove(k);
  }
  void opIndexAssign(V v, K k) {
    debug assert(v == true);
    foreach (i, key; FastKeys) {
      if (k == key) { fastkeys[i] = true; return; }
    }
    hash[k] = v;
  }
}

// tools.threads.TLS!(Stuple!(Transaction[], bool)[]) freelist;
tools.threads.TLS!(Stuple!(Transaction[], int)) cachething;
Transaction[] allocTransactionList(int len) {
  if (!len) return null;
  auto thing = cachething.ptr();
  if (len > 1024) return new Transaction[len];
  if (thing._0.length - thing._1 < len) { thing._0 = new Transaction[16384]; thing._1 = 0; }
  auto res = thing._0[thing._1 .. thing._1 + len];
  thing._1 += len;
  return res;
  /*auto free = *freelist.ptr();
  foreach (ref entry; free) {
    if (!entry._1 && entry._0.length >= len) {
      entry._1 = true; // in use
      return entry._0[0..len];
    }
  }
  return new Transaction[len];*/
}

void markUnused(Transaction[] t) {
  /*auto free = *freelist.ptr();
  foreach (ref entry; free) {
    if (entry._0.ptr == t.ptr) {
      entry._1 = false;
      if (t.length > entry._0.length) entry._0 = t;
      return;
    }
  }
  if (!t.length) return;
  free ~= stuple(t, false);
  *freelist.ptr() = free;*/
}

tools.threads.TLS!(ProcTrack[]) proctrack_cachething;

void markProctrackDone(ProcTrack pt) {
  auto list = *proctrack_cachething.ptr();
  foreach (ref entry; list) { if (!entry) { entry = pt; return; } }
  list ~= pt;
  *proctrack_cachething.ptr() = list;
}

ProcTrack allocProctrack() {
  auto list = *proctrack_cachething.ptr();
  foreach (ref entry; list) {
    if (entry) {
      auto res = entry;
      res.clear;
      entry = null;
      return res;
    }
  }
  return new ProcTrack;
}

struct XArray(T) {
  T[] back;
  int len;
  int length() { return len; }
  void clear() { len = 0; }
  T[] opCall() { return back[0..len]; }
  string toString() { return Format(back[0..len]); }
  static XArray opCall(T[] list, int len) {
    XArray res;
    res.back = list;
    res.len = len;
    return res;
  }
  int opApply(int delegate(ref T) dg) {
    foreach (ref entry; back[0..len])
      if (auto res = dg(entry)) return res;
    return 0;
  }
  void shrink(int by) {
    len -= by;
    debug assert(len >= 0);
  }
  static if (is(T == string)) {
    void opCatAssign(T t) {
      if (len == back.length) { back ~= t; len ++; }
      else { back[len++] = t; }
    }
  } else {
    void opCatAssign(ref T t) {
      if (len == back.length) { back ~= t; len ++; }
      else { back[len++] = t; }
    }
  }
}

// track processor state
// obsoletes about a dozen peephole opts
class ProcTrack : ExtToken {
  alias Tuple!("%ebp", "%esp", "%eax", "%ebx", "%ecx", "%edx", "%esi") CommonKeys;
  OrderedFastHashlike!(string, string) known;
  XArray!(string) stack; // nativePtr-sized
  XArray!(string) latepop;
  // in use by this set of transactions
  // emit before overwriting
  SmartHashmap!(bool, string, CommonKeys) use;
  // backup
  XArray!(Transaction) backup, knownGood;
  // not safe to mix foo(%ebp) and foo(%esp) in the same proc chunk
  int ebp_mode = -1;
  int eaten;
  int postfree;
  bool noStack; // assumed no stack use; don't challenge this
  int stackdepth = -1; // stack depth at start
  // reset to pristine state
  void clear() {
    known.clear;
    stack.clear;
    latepop.clear;
    use.clear;
    backup.clear; knownGood.clear;
    ebp_mode = -1; eaten = 0; postfree = 0; noStack = false; stackdepth = -1;
  }
  string toString() {
    return Format("cpu(",
      (stackdepth != -1)?Format("@", stackdepth):"@?", " ",
      isValid?"[OK]":"[BAD]", " ", known,
      ", stack", noStack?"[none] ":" ", stack.length, "; ", stack,
      ", pop ", latepop, /*", used ", use.keys,*/
    ")");
  }
  int getStackDelta() {
    return - stack.length * 4 + latepop.length * 4;
  }
  string mkIndirect(string val, int delta = 0 /* additional delta */) {
    if (val.startsWith("+(")) {
      auto op2 = val.between("(", ")"), op1 = op2.rslice(",").strip();
      if (op1.startsWith("%gs:")) return null;
      op2 = op2.strip();
      bool isReg;
      if (op1.find(",") != -1) isReg = true; // %reg,%reg
      else isReg = op1.isRegister();
      if (isReg && op2.isNumLiteral()) {
        auto op2i = op2.literalToInt();
        /*if (t.to in use)
          return null;*/
        // to indirect access
        auto sumdelt = op2i + delta;
        if (sumdelt) return qformat(sumdelt, "(", op1, ")");
        else return qformat("(", op1, ")");
      }
    }
    return null;
  }
  // does this super-instruction modify the stack?
  bool modsStack() {
    return stack.length || latepop.length;
  }
  bool update(Transaction t) {
    if (t.stackdepth != -1 && !modsStack()) {
      if (stackdepth == -1) stackdepth = t.stackdepth;
      else if (stackdepth != t.stackdepth) {
        logln("tried to update proctrack with invalid stack depth: ", t.stackdepth, " but we have ", stackdepth);
        logln(t, " into ", this);
        fail;
      }
    }
    info(t).accessParams((ref string s) { s = s.cleanup(); });
    scope(exit) {
      if (isValid) {
        knownGood = translate();
        // nuh!
        // use = null; // effectively restarting
        backup.clear;
      }
    }
    bool partialKnown(string s) {
      foreach (key, value; known) if (s.contains(key)) return true;
      return false;
    }
    // #define .. lol
    const string Success = "{ backup ~= t; eaten ++; return true; }";
    bool canOverwrite(string s, string whs = null) {
      if (  s in known && known[  s] == whs) return true;
      foreach (entry; stack)
        if (entry.find(s) != -1) return false;
      foreach (key, value; known) {
        if (s.contains(key) && s != key) return false;
        if (value.find(s) != -1) return false;
      }
      return true;
    }
    bool set(string mem, string val) {
      bool checkMode(string s) {
        if (s.find("%esp") != -1) {
          if (ebp_mode == -1) ebp_mode = false;
          else if (ebp_mode == true) return false;
        }
        if (s.find("%ebp") != -1) {
          if (ebp_mode == -1) ebp_mode = true;
          else if (ebp_mode == false) return false;
        }
        return true;
      }
      if (!checkMode(mem) || !checkMode(val)) return false;
      if (mem == val) known.remove(mem);
      else {
        if (val) { // if val is null, this is equivalent to void assignment. do nothing.
          if (mem.isRelative() && val.isRelative())
            return false;
          if (!(mem in known) && mem in use) // fallen out of use
            use.remove(mem);
          known[mem] = val;
        } else return false;
      }
      return true;
    }
    if (t.kind != Transaction.Kind.Nevermind) {
      if (latepop.length && t.kind != Transaction.Kind.Pop)
                         return false;
    }
    // Note: this must NOT fix up the stack! think about it.
    bool _fixupESPDeps(bool _try, int shift) {
      typeof(known) newknown;
      foreach (key, value; known) {
        if (_try) {
          if (!tryFixupString(key, shift) || !tryFixupString(value, shift))
            return false;
        } else {
          fixupString(key, shift);
          fixupString(value, shift);
        }
        newknown[key] = value;
      }
      known = newknown;
      return true;
    }
    void fixupESPDeps(int shift) { _fixupESPDeps(false, shift); }
    bool tryFixupESPDeps(int shift) { return _fixupESPDeps(true, shift); }
    with (Transaction.Kind) switch (t.kind) {
      case Compare: return false;
      case LoadAddress:
        if (t.to.isRegister()) {
          if (t.to in use) break;
          int delta;
          if (auto reg = t.from.isIndirect2(delta)) {
            if (reg in known && reg == t.to) return false; // circle
            if (!delta /* effectively a mov */ && !reg.contains("%esp") /* unreliable */) {
              if (!set(t.to, reg))
                return false;
            } else {
              if (!set(t.to, qformat("+(", reg, ", $", delta, ")")))
                return false;
            }
            use[reg] = true;
            mixin(Success);
          }
        }
        break;
      case MathOp:
        if (t.opName == "imull" && t.op1 == "$1"
         || t.opName == "addl" && t.op1 == "$0"
         || t.opName == "subl" && t.op1 == "$0") {
          mixin(Success);
        }
        string op2 = t.op2;
        if (auto p = op2 in known) op2 = *p;
        
        if (t.opName != "addl") break;
        if (t.op1.isNumLiteral() && t.op2 in known) {
          auto stuf = known[t.op2];
          if (stuf.isRegister()) {
            if (!set(t.op2, qformat("+(", known[t.op2], ", $", t.op1.literalToInt(), ")")))
              return false;
            mixin(Success);
          } else if (stuf.startsWith("+(")) {
            auto mop2 = stuf.between("+(", ")"), mop1 = mop2.slice(", ");
            if (mop2.isNumLiteral()) {
              if (!set(t.op2, qformat("+(",
                mop1,
                ", $", mop2.literalToInt() + t.op1.literalToInt(),
              ")")))
                return false;
              mixin(Success);
            }
          }
          return false;
        }
        if (t.op1.isNumLiteral() && t.op2 == "(%esp)" && stack.length && stack()[$-1].startsWith("+(")) {
          auto mop2 = stack()[$-1].between("+(", ")"), mop1 = mop2.slice(", ");
          if (mop2.isNumLiteral()) {
            stack()[$-1] = qformat("+("[], mop1, ", $"[], mop2.literalToInt() + t.op1.literalToInt(), ")"[]);
            mixin(Success);
          }
        }
        break;
      case SAlloc:
        if (noStack) return false;
        if (t.size % 4 == 0) {
          for (int i = 0; i < t.size / 4; ++i)
            stack ~= null;
          fixupESPDeps(t.size);
          mixin(Success);
        } else break;
      case SFree:
        if (t.size % nativePtrSize != 0) return false;
        auto st2 = stack;
        for (int i = 0; i < t.size / nativePtrSize; ++i)
          if (st2.length) st2.shrink(1);
          else return false;
        if (!tryFixupESPDeps(-4 * (stack.length - st2.length)))
          return false;
        stack = st2;
        mixin(Success);
      case MovD:
        if (t.from.isSSERegister() || !t.to.isSSERegister()) return false;
      case Mov:
        if (t.to == "%esp")
          return false;
        
        if (t.from == "%esp")
          return false; // TODO: can this ever be handled?
        if (t.from in known && known[t.from] == t.to) {
          // circular write, lol
          mixin(Success);
        }
        if (!canOverwrite(t.to, t.from)) break; // lol
        if (t.to.isIndirect().contains("%esp"))
          use["%esp"] = true;
        if (t.from.isIndirect() == t.to) return false; // (eax) -> eax; can't handle this
        int delta;
        if (t.from.isRegister()) {
          string src = t.from;
          bool unsafe;
          if (auto p = src in known) {
            auto src2 = *p;
            // would cause a mem move
            // TODO debug
            /*if (src2.isRelative() && t.to.isRelative()) { }
            else */
              src = src2;
            if (src.isIndirect()) unsafe = true;
          }
          use[src] = true;
          if (t.to.isRegister()) {
            if (!set(t.to, src))
              return false;
          } else if (t.to == "(%esp)") {
	    if (unsafe) return false;
            if (!stack.length) {
              if (latepop.length) break;
              auto mysrc = src;
              if (mysrc.isIndirect()) mysrc = t.from;
              if (!set(t.to, mysrc)) // t.from, not src, to prevent mem-to-mem movs
                return false;
              use[mysrc] = true;
              noStack = true;
              mixin(Success);
            }
            stack()[$-1] = src;
          } else {
            if (!set(t.to, src))
              return false;
          }
          mixin(Success);
        } else if (t.from in known && known[t.from].isLiteral()) {
          if (!set(t.to, known[t.from]))
            return false;
          mixin(Success);
        } else if (auto deref = t.from.isIndirect2(delta)) {
          // TODO: handle this (stuff like '0(%eax, %ecx)')
          if (deref.find(",") != -1) return false;
          if (deref in known) {
            auto val = known[deref];
            if (auto indir = mkIndirect(val, delta)) {
              if (!set(t.to, indir))
                return false;
              mixin(Success);
            }
          }
          if (partialKnown(deref)) return false;
          // if (deref == "%esp") logln("delta ", delta, " to ", t.to, " and we are ", this);
          if (deref == "%esp" && t.to.isUtilityRegister() && !(delta % 4)) {
            auto from_rel = delta / 4;
            if (stack.length >= from_rel + 1) {
              auto index = stack.length - 1 - from_rel;
              // can't just read stack - the stack address is understood to be only valid during stack building phase
              // auto val = stack[$ - 1 - from_rel];
              // instead "unroll" the stack until the index is _just_ at length, then set the value and uproll
              auto fixdist = 4 * (stack.length - index);
              auto src = stack()[index];
              fixupString(src, fixdist);
              if (!set(t.to, src))
                return false;
              mixin(Success);
            } else {
              string src = cleanup(t.from);
              if (auto nsrc = src in known)
                src = *nsrc;
              if (!set(t.to, src))
                return false;
              mixin(Success);
            }
          }
          if (t.to.isUtilityRegister() && !(deref in known) && deref != "%esp") {
            if (!set(t.to, t.from))
              return false;
            mixin(Success);
          }
          return false;
          break;
        } else if (t.from.isLiteral()) {
          int offs;
          auto indir = t.to.isIndirect2(offs);
          if (indir == "%esp" || (indir == "%ebp" && offs < 0))
            // access to live stack
            if (stack.length) return false;
            else noStack = true;
          if (!set(t.to, t.from))
            return false;
          mixin(Success);
        }
        break;
      case Label: return false;
      case Push:
        if (noStack || "%esp" in use)
          return false;
        if (t.size == nativePtrSize) {
          int offs;
          if (auto src = t.source.isIndirect2(offs)) {
            if (src == "%esp") {
              bool hasMemoryAccess;
              foreach (key, value; known) if (key.find("(")!=-1 || value.find("(")!=-1) hasMemoryAccess = true;
              // really not safe!
              if (hasMemoryAccess) return false;
            }
            if (src in known) {
              if (auto indir = mkIndirect(known[src], offs)) {
                if (auto id = indir.isIndirect())
                  // depends on a register that we've yet to emit on stackbuild time
                  if (partialKnown(id)) return false;
                fixupESPDeps(4);
                
                stack ~= indir;
                mixin(Success);
              }
            }
            if (partialKnown(src)) return false;
          }
          auto val = t.source;
          if (val.isLiteral() && !known.length /* avoid colliding with direct_push_after_mov */) {
            stack ~= val;
            mixin(Success);
          }
          if (auto p = t.source in known)
            val = *p;
          // Be VERY careful changing this
          // remember, push is emat before mov!
          // [edit] That's alright now, we can just update the ESP of knowns.
          // if (val in known) return false;
          // increment our knowns.
          // logln("also I am ", this);
          if (!val.isMemAccess()) {
            if (known.length && !(t.source in known)) return false; // workaround
          }
          if (auto reg = val.isIndirect2(offs)) {
            if (reg in known) return false; // bad dependence ordering
            // possible stack/variable dependence. bad.
            // TODO: only abort if we have outstanding stack writes
            if (reg == "%ebp" && offs < 0 && known.length)
              return false;
            if (reg == "%esp") {
              if (offs % 4 == 0) {
                auto id = offs / 4;
                if (id >= 0 && id < stack.length) {
                  auto newsrc = stack()[stack.length-1-id];
                  fixupString(newsrc, (id + 1) * 4); // we're deeper into the stack than we were then!
                  fixupESPDeps(4);
                  stack ~= newsrc;
                  mixin(Success);
                }
              }
              // return false;
            }
            use[reg] = true;
          }
          if (val.isRegister()) use[val] = true;
          fixupESPDeps(4);
          stack ~= val;
          mixin(Success);
        }
        if (t.source.isLiteral()) {
          if (t.size % nativePtrSize != 0)
            return false; // not a case we can handle
          auto steps = t.size / nativePtrSize;
          for (int i = 0; i < steps; ++i)
            stack ~= t.source;
          mixin(Success);
        }
        break;
      case Pop:
        if (t.size != nativePtrSize) return false;
        if (t.dest.isRegister()) {
          if (!stack.length) break;
          if (t.dest != stack()[$-1]) {
            foreach (entry; stack)
              if (entry.find(t.dest) != -1) return false;
          }
          //   if (&& t.dest in use) return false;
          // do this first because pushed addresses were evaluated before the push took place
          fixupESPDeps(-4);
          if (!set(t.dest, stack()[$-1])) {
            fixupESPDeps(4); // undo
            return false;
          }
          stack.shrink(1);
          mixin(Success);
        }
        int offs;
        if (auto dest = t.dest.isIndirect2(offs)) {
          if (dest in known) {
            if (auto indir = mkIndirect(known[dest], offs)) {
              // if (!stack.length && latepop.length) break;
              if (stack.length) {
                auto newval = stack()[$-1];
                if (newval.find("%esp") == -1 || (newval.find("%ebp") == -1 && offs < 0))
                  // not reliable to do push/pop stackwork before we move to the active stack
                  if (stack.length) return false;
                  else noStack = true;
                if (!indir.tryFixupString(-4)) // this absorbs a pop. account for that.
                  return false;
                if (!set(indir, newval))
                  return false;
                // we have a pop! fix up the esp deps
                fixupESPDeps(-4);
                stack.shrink(1);
                mixin(Success);
              } else {
                auto len = latepop.length;
                if (!tryFixupESPDeps(-4 * len))
                  return false;
                latepop ~= mkIndirect(known[dest], offs); // re-eval indir for fixup
                fixupESPDeps(4 * len); // and undo
                mixin(Success);
              }
            }
          } else if (dest == "%esp" && stack.length && !(offs % 4) && offs / 4 < stack.length && !isMemRef(stack()[$-1])) {
            auto val = stack()[$-1];
            fixupString(val, 4);
            auto id = offs / 4;
            stack()[$-1 - id] = val;
            fixupESPDeps(-4);
            stack.shrink(1);
            mixin(Success);
          } else if (dest == "%esp" || dest.isUtilityRegister()) {
            if (stack.length && !isMemRef(stack()[$-1])) {
              auto val = stack()[$-1];
              fixupString(val, 4);
              if (!set(t.dest, val))
                return false;
              fixupESPDeps(-4);
              stack.shrink(1);
              mixin(Success);
            }
          }
          return false;
        }
        break;
      case Nevermind: return false;
      case Call: return false;
      case Jump: return false;
      case FloatLoad, FloatIntLoad: return false;
      default: break;
    }
    return false;
    logln("---- Unsupported: ", t);
    logln("state ", this);
    fail;
  }
  bool isValid() {
    foreach (entry; stack) {
      if (auto rest = entry.startsWith("+(")) {
        return false;
      }
    }
    foreach (mem, value; known) {
      if (!value) return false; // #INV
      if (auto rest = value.startsWith("+("))
        if (!mem.isRegister())
          return false;
        else
          continue;
      // TODO: move over eax or something
      if (mem.isRelative() && value.isRelative()) return false;
    }
    return true;
  }
  XArray!(Transaction) translate() {
    Transaction[] res;
    int reslen;
    if (!isValid()) {
      res = allocTransactionList(knownGood.length + backup.length);
      res[0..knownGood.length] = knownGood();
      res[knownGood.length .. $] = backup();
      reslen = res.length;
    } else {
      res = allocTransactionList(stack.length + known.length + latepop.length);
      int myStackdepth; // local offs
      bool sd = stackdepth != -1;
      void addTransaction(Transaction.Kind tk,
        void delegate(ref Transaction) dg,
        void delegate(ref Transaction) dg2 = null
        ) {
        Transaction t;
        t.kind = tk;
        if (sd) t.stackdepth = stackdepth + myStackdepth;
        void fixup(ref string st) {
          int offs;
          /*if ("%esp" == st.isIndirect2(offs)) {
            // fix
            auto delta = offs + myStackdepth;
            if (delta)
              st = qformat(delta, "(%esp)");
            else
              st = "(%esp)";
          }*/
        }
        dg(t);
        info(t).accessParams(&fixup);
        if (dg2) dg2(t);
        
        if (res.length == reslen) {
          auto backup = res;
          res ~= t;
          if (backup.ptr !is res.ptr) {
            markUnused(backup); // append reallocated
          }
          reslen ++;
        }
        else { res[reslen++] = t; }
      }
      if (stack.length && noStack) {
        logln("Highly invalid processor state: ", this);
        fail;
      }
      int toAlloc;
      void flushAllocs() {
        if (!toAlloc) return;
        addTransaction(
          Transaction.Kind.SAlloc,
          (ref Transaction t) { t.size = toAlloc; },
          (ref Transaction t) { myStackdepth += toAlloc; }
        );
        toAlloc = 0;
      }
      foreach (entry; stack) {
        entry = entry.strip();
        if (entry.length) {
          flushAllocs;
          addTransaction(Transaction.Kind.Push, (ref Transaction t) {
            t.source = entry;
            t.size = 4;
          }, (ref Transaction t) {
            myStackdepth += nativeIntSize;
          });
        } else toAlloc += 4;
      }
      flushAllocs;
      void walkKnown(bool delegate(string from, string to) dg) {
        foreach (reg, value; known) {
          if (!dg(value, reg)) continue;
          if (auto indir = mkIndirect(value)) {
            addTransaction(Transaction.Kind.LoadAddress, (ref Transaction t) {
              t.from = indir; t.to = reg;
            });
          } else {
            if (reg.isSSERegister())
              addTransaction(Transaction.Kind.MovD, (ref Transaction t) {
                t.from = value; t.to = reg;
              });
            else
              addTransaction(Transaction.Kind.Mov, (ref Transaction t) {
                t.from = value; t.to = reg;
              });
          }
        }
      }
      auto isalea = (string from, string to) { return !!mkIndirect(from); };
      // pull ahead all moves into registers that become sources for latter moves
      auto first = (string from, string to) {
        if (!to.isUtilityRegister()) return false;
        if (isalea(from, to)) return false;
        foreach (to2, from2; known) {// O n squared, bitch. That's how we roll.
          if (from2 == to) return true;
        }
        return false;
      };
      walkKnown(first);
      walkKnown((string from, string to) { return !first(from, to) && !isalea(from, to); });
      walkKnown(isalea);
      foreach (entry; latepop) {
        addTransaction(Transaction.Kind.Pop, (ref Transaction t) {
          t.dest = entry;
          t.size = 4;
        }, (ref Transaction t) {
          myStackdepth -= nativeIntSize;
        });
      }
    }
    return XArray!(Transaction) (res, reslen);
  }
  string toAsm() { assert(false); }
}

bool delegate(Transcache, ref int[string]) ext_step;

bool x86optsSetup;
void setupX86Opts() {
  synchronized {
    if (x86optsSetup) return;
    x86optsSetup = true;
  }
  bool goodMovSize(int i) { return i == 4 || i == 2 || i == 1; }
  mixin(opt("ebp_to_esp", `*:
    info($0).hasIndirect("%ebp")
    && $0.hasStackdepth && info($0).opSize != 1
    =>
    $T t = $0;
    bool changed;
    void doStuff(ref string str) {
      auto offs = str.between("", "(").my_atoi(); 
      auto new_offs = offs + t.stackdepth;
      if (new_offs) str = qformat(new_offs, "(%esp)");
      else str = "(%esp)";
      changed = true;
    }
    bool skip;
    /*if ($0.kind == $TK.Push /or/ $TK.Pop) {
      // if we can't do the push in one step
      if ($0.size != 4 /or/ 2 /or/ 1) 
        skip = true;
    }*/
    if (!skip) {
      info(t).accessParams((ref string s) { if (s.isIndirect().contains("%ebp")) doStuff(s); });
      if (changed) $SUBST(t);
    }
  `));
  mixin(opt("ext_step", `*, *
    =>
    ProcTrack obj;
    $T t;
    t.kind = $TK.Extended;
    auto first = $0;
restart:
    if (first.kind == $TK.Extended) {
      obj = cast(ProcTrack) first.obj;
      t.obj = obj;
      bool couldUpdate = obj.update($1);
      if (couldUpdate) {
        $SUBST(t);
        // in case you're wondering .. yeah I'm just trolling my future self here.
        if (match.to != match.parent.list.length) {
          goto skip; // > > > \ 
        } //                   v
      } //                     v
      auto res = obj./*        v */translate()();
      bool progress = /*       v */res.length != obj.eaten;
      if (couldUpdate) /*      v */ $SUBST(res);
      else $SUBST(res, $1); // v
      markUnused(res); //      v
      markProctrackDone(obj);//v
      if (!progress) //        v
        match.modded = /*      v */ false; // meh. just skip one
      _changed = progress; //  v secretly
      skip:; //    < < < < < < /
    } else {
      if (xpar == -1 || si < xpar) {
        si++;
        obj = allocProctrack();
        t.obj = obj;
        if (obj.update(first)) {
          // $SUBST(t, $1);
          first = t;
          goto restart;
        }
        // else logln("Reject ", $0, ", ", $1);
        markProctrackDone(obj);
      }
    }
  `));
  // .ext_step = &ext_step; // export
  // opts = opts[0 .. $-1]; // only do ext_step once
  
  mixin(opt("rewrite_zero_ref", `*:
    info($0).hasOps
    =>
    auto t = $0;
    bool changed;
    info(t).accessParams((ref string s) {
      if (s.startsWith("0(")) {
        s = s[1 .. $]; changed = true;
      }
    });
    if (changed) $SUBST(t);
  `));
  // alloc/free can be shuffled up past anything that doesn't reference stack.
  mixin(opt("skip_forget", `^LoadAddress, ^SFree, ^Nevermind: $0.to == $2.dest => $SUBST($1); `));
  mixin(opt("sort_pointless_mem", `*, ^SAlloc || ^SFree:
    info($0).hasOps
    =>
    int shift = -1;
    $T t = $0.dup;
    bool dontDoIt;
    void detShift(string s) {
      if (!s.isIndirect().contains("%esp")) {
        int offs;
        if (s.isIndirect2(offs) == "%ebp" && offs < 0)
          dontDoIt = true; // may refer to stack-in-use
        if (s.isIndirect().hasUtilityRegister()) dontDoIt = true; // might still point at the stack.
        if (s == "%esp") dontDoIt = true; // duh
        return;
      }
      auto offs = s.between("", "(").my_atoi();
      if ($1.kind == $TK.SAlloc) {
        shift = $1.size; // move it all to front
      } else {
        if (shift == -1) {
          shift = min($1.size, offs);
        } else {
          shift = min(shift, offs);
        }
      }
    }
    void applyShift(ref string s) {
      if (!s.isIndirect().contains("%esp")) return;
      auto offs = s.between("", "(").my_atoi();
      if ($1.kind == $TK.SAlloc) {
        s = qformat(offs + shift, "("[], s.isIndirect(), ")"[]);
      } else {
        s = qformat(offs - shift, "("[], s.isIndirect(), ")"[]);
      }
    }
    info(t).accessParams((ref string s) { detShift(s); });
    // ------------------------------
    info(t).accessParams((ref string s) { applyShift(s); });
    bool substed;
    // override conas
    if ((
      !changesOrNeedsActiveStack($0) ||
      $0.kind == $TK.Mov /or/ $TK.MovD /or/ $TK.FloatPop /or/ $TK.FPIntPop /or/ $TK.FPLongPop /or/ $TK.DoublePop /or/
      $TK.FloatLoad /or/ $TK.FloatStore /or/ $TK.DoubleStore /or/ $TK.LoadAddress /or/ $TK.SSEOp
    ) && ((shift > 0 || shift == -1) && !dontDoIt)) {
      if (shift == -1) shift = $1.size;
      auto t0 = $1, t2 = $1;
      t0.size = shift; t2.size -= shift;
      if (t.hasStackdepth)
        if ($1.kind == $TK.SAlloc)
          t.stackdepth += shift;
        else
          t.stackdepth -= shift;
      $T[] res = [t];
      if (t0.size) res = [t0] ~ res;
      if (t2.size) res = res ~ [t2];
      if (t0.size) {
        $SUBST(res);
        substed = true;
      }
    }
    // if (!substed) logln("sort_pointless_mem: ", [$0, $1], ", shift of ", shift, " dontDoIt is ", dontDoIt, " conas is ", changesOrNeedsActiveStack($0));
  `));
  mixin(opt("make_call_direct", `^Mov, ^Call: $0.to == $1.dest => $SUBSTWITH { kind = $TK.Call; dest = $0.from; } `));
  
  // jump opts
  mixin(opt("join_labels", `^Label, ^Label => auto t = $0; t.names ~= $1.names; t.keepRegisters |= $1.keepRegisters; $SUBST(t); `));
  mixin(opt("pointless_jump", `^Jump, ^Label:
    $1.hasLabel($0.dest)
    =>
    l_refc[$0.dest] --;
    if (!l_refc[$0.dest]) $SUBST();
    else $SUBST($1);
  `));
  mixin(opt("move_lea_down", `^LoadAddress, *:
    $1.kind != $TK.LoadAddress && ($1.kind != $TK.Mov || !$1.from.isLiteral() || $1.from.isNumLiteral()) && !pinsRegister($1, $0.to) &&
    !$0.from.contains(info($1).outOp())
    =>
    $T t = $0;
    bool remove;
    auto size1 = info($1).opSize;
    auto it = info(t);
    bool skip;
    if (info($1).growsStack) it.fixupStack( size1);
    if (info($1).shrinksStack) {
      if (it.couldFixup(-size1))
        it.fixupStack(-size1);
      else skip = true;;
    }
    if (!skip) $SUBST($1, t);
  `));
  mixin(opt("move_lea_downer", `^LoadAddress, ^SFree, *:
    $2.kind != $TK.LoadAddress &&
    !pinsRegister($2, $0.to) && !info($2).resizesStack()
    =>
    $T t = $2.dup;
    info(t).fixupStack($1.size);
    $SUBST(t, $0, $1);
  `));
  mixin(opt("wat", `^LoadAddress, ^Pop||^SFree:
    !info($1).opContains($0.to) && ($1.kind == $TK.SFree || !info($0).opContains($1.dest))
    =>
    auto t = $0.dup;
    bool block;
    if (!t.from.tryFixupString(-$1.size)) block = true;
    if (!block) $SUBST($1, t);
  `));
  // Seriously, what the hell.
  mixin(opt("excuse_me_but_WAT", `^Mov, ^MathOp:
    $0.from.isNumLiteral() && $0.to.isUtilityRegister() &&
    ($1.op1 == $0.to || $1.opName == "addl"[] /or/ "imull"[] && $1.op2 == $0.to)
    =>
    $T t = $1;
    if (t.op1 != $0.to) { // commutative op with lit on op2
      if (t.op1.isNumLiteral()) {
        int n = $0.from.literalToInt();
        if ($1.opName == "addl") n += t.op1.literalToInt();
        else n *= t.op1.literalToInt();
        $T t2 = $0;
        t2.from = qformat("$"[], n);
        $SUBST(t2);
      } else {
        $T t2 = $0;
        t2.from = t.op1;
        t.op1 = $0.from;
        $SUBST(t2, t);
      }
    } else {
      t.op1 = $0.from;
      $SUBST(t, $0);
    }
  `));
  /*mixin(opt("further_tweakage", `^LoadAddress, ^MathOp:
    $0.to == $1.op2 && $0.from.isIndirect().hasUtilityRegister() &&
    $1.op1.isNumLiteral() && $1.op1.literalToInt() <= 3
    =>
    int offs;
    auto reg = $0.from.isIndirect2(offs);
    $T t = $0;
    t.
  `));*/
  mixin(opt("break_circle_confusion", `^LoadAddress || ^Mov || ^MathOp, ^LoadAddress || ^Mov:
    ($0.kind != $TK.Mov || $1.kind != $TK.Mov) &&
    ($0.kind != $TK.MathOp || $0.opName == "addl" && $0.op1.isNumLiteral())
    =>
    string t0from, t0to, t1from, t1to;
    int sum;
    if ($0.kind == $TK.Mov) {
      t0from = $0.from;
      t0to = $0.to;
    } else if ($0.kind == $TK.MathOp) {
      t0from = $0.op2;
      sum += $0.op1.literalToInt();
      t0to = $0.op2;
    } else {
      int s;
      if (auto indir = $0.from.isIndirect2(s)) { t0from = indir; sum += s; }
      else t0from = $0.from;
      t0to = $0.to;
    }
    if ($1.kind == $TK.Mov) {
      t1from = $0.from;
    } else {
      int s;
      if (auto indir = $1.from.isIndirect2(s)) { t1from = indir; sum += s; }
      else t1from = $1.from;
    }
    t1to = $1.to;
    if (t0to == t1from && t1to == t0from && t0from.isUtilityRegister() && t0to.isUtilityRegister()) {
      if (sum != 0) {
        $T t0;
        t0.kind = $TK.LoadAddress;
        t0.from = qformat(sum, "("[], t0from, ")"[]);
        t0.to = t0from;
        if (t0to == t0.to) $SUBST(t0);
        else $SUBST($0, t0);
      } else {
        if (t0from == t0to) {
          $SUBST();
        } else {
          $SUBST($0);
        }
      }
    }
  `));
  mixin(opt("push_movd_into_direct_movd", `^Push, ^SSEOp:
    $0.size == 4 &&
    $1.opName == "movd" && $1.op2.isSSERegister() && $1.op1 == "(%esp)"
    =>
    $T t = $1.dup;
    t.op1 = $0.source;
    if (t.op1 == "$" "0" /* cheat, on account of $ 0 being substituted with the first parameter */) {
      t.op1 = t.op2;
      t.opName = "xorps";
      $SUBST(t, $0);
    } else if (t.op1.isIndirect()) {
      $SUBST(t, $0);
    }
  `));
  mixin(opt("math_after_load", `^SSEOp, ^SSEOp:
    $0.opName == "xorps" /* todo: expand as needed */ && $1.opName == "movd" /* todo: expand as needed */ &&
    $0.op1.isSSERegister() && $0.op2.isSSERegister() &&
    !$1.op1.isSSERegister() && $1.op2.isSSERegister() &&
    $1.op2 != $0.op1 && $1.op2 != $0.op2
    =>
    $SUBST($1, $0);
  `));
  mixin (opt("push_after_mov_ps", `^Push, ^SSEOp:
    $0.size == 4 && $0.source.isUtilityRegister() &&
    $1.opName == "movaps"[] /or/ "movups"[] && !info($1).opContains($0.source) && info($1).couldFixup(-4)
    =>
    $T t = $1.dup;
    info(t).fixupStack(-4);
    $SUBST(t, $0);
  `));
  // movd %xmm0 -> (%eax); movd (%eax) -> %xmm0 ==> movd %xmm0 -> (%eax)
  /*mixin(opt("redundant_move", `^SSEOp, ^SSEOp:
    $0.opName == "movd" && $1.opName == "movd" && $0.op1.isSSERegister() &&
    $0.op1 == $1.op2 && $1.op1 == $0.op2
    =>
    $SUBST($0);
  `));*/
  mixin(opt("direct_vector_load", `^Mov, ^Push, ^Push, ^Push, ^Push, ^SSEOp:
    $5.opName == "movaps"[] /or/ "movups"[] && $5.op2.isSSERegister() && $5.op1 == "(%esp)" &&
    $0.to.isUtilityRegister() && $1.size /and/ $2.size /and/ $3.size /and/ $4.size == 4 &&
    $1.source.isIndirect() == $0.to && $2.source.isIndirect() == $0.to && $3.source.isIndirect() == $0.to && $4.source.isIndirect() == $0.to
    =>
    int d1, d2, d3, d4;
    $1.source.isIndirect2(d1); $2.source.isIndirect2(d2); $3.source.isIndirect2(d3); $4.source.isIndirect2(d4);
    if (d1-4==d2 && d2-4==d3 && d3-4==d4) {
      auto t1 = $0.dup;
      $T t2;
      t2.kind = $TK.SAlloc;
      t2.size = 16;
      auto t3 = $5.dup;
      t3.opName = "movups";
      t3.op1 = $4.source;
      $SUBST(t1, t2, t3);
    }
  `));
  mixin(opt("direct_vector_store", `^SSEOp, ^Mov, ^Pop, ^Pop, ^Pop, ^Pop:
    $0.opName == "movaps"[] /or/ "movups"[] && $0.op1.isSSERegister() && $0.op2 == "(%esp)" &&
    $1.to.isUtilityRegister() && $2.size /and/ $3.size /and/ $4.size /and/ $5.size == 4 &&
    $2.dest.isIndirect() == $1.to && $3.dest.isIndirect() == $1.to && $4.dest.isIndirect() == $1.to && $5.dest.isIndirect() == $1.to
    =>
    int d1, d2, d3, d4;
    $2.dest.isIndirect2(d1); $3.dest.isIndirect2(d2); $4.dest.isIndirect2(d3); $5.dest.isIndirect2(d4);
    if (d1+4==d2 && d2+4==d3 && d3+4==d4) {
      auto t1 = $0.dup;
      t1.opName = "movups";
      t1.op2 = $2.dest;
      auto t2 = $1.dup;
      if (t2.from.tryFixupString(-16)) {
        $T t3;
        t3.kind = $TK.SFree;
        t3.size = 16;
        $SUBST(t3, t2, t1);
      }
    }
  `));
  mixin(opt("direct_vector_stack_store", `^SSEOp, ^Pop, ^Pop, ^Pop, ^Pop:
    $0.opName == "movaps"[] /or/ "movups"[] && $0.op1.isSSERegister() && $0.op2 == "(%esp)" &&
    $1.size /and/ $2.size /and/ $3.size /and/ $4.size == 4 &&
    $1.dest.isIndirect() /and/ $2.dest.isIndirect() /and/ $3.dest.isIndirect() /and/ $4.dest.isIndirect() == "%esp"
    =>
    int d1, d2, d3, d4;
    $1.dest.isIndirect2(d1); $2.dest.isIndirect2(d2); $3.dest.isIndirect2(d3); $4.dest.isIndirect2(d4);
    if (d1==d2 && d2==d3 && d3==d4) {
      auto t1 = $0.dup;
      t1.opName = "movups";
      t1.op2 = $1.dest;
      $T t2;
      t2.kind = $TK.SFree;
      t2.size = 16;
      $SUBST(t1, t2);
    }
  `));
  mixin(opt("dont_be_silly", `^SSEOp, ^SAlloc||^SFree:
    $0.opName == "movaps"[] /or/ "movups"[] && $0.op1.isIndirect().hasUtilityRegister() && $0.op2.isSSERegister()
    =>
    $SUBST($1, $0.dup);
  `));
  mixin(opt("load_address_into_source", `^LoadAddress, *:
    info($1).hasIndirectEq($0.to) && info($1).opSize() > 1
    =>
    $T t = $1;
    info(t).accessParams((ref string st) {
      int offs;
      if (st.isIndirect2(offs) == $0.to) {
        int offs2;
        string srcreg = $0.from.isIndirect2(offs2);
        if (!srcreg) { offs2 = 0; srcreg = $0.from; }
        st = qformat(offs + offs2, "("[], srcreg, ")"[]);
      }
    });
    $T t2 = $0;
    bool allow = true;
    if (info($1).growsStack)   {
      info(t2).fixupStack( info($1).opSize());
    }
    if (info($1).shrinksStack) {
      if (!info(t2).couldFixup(-info($1).opSize()))
        allow = false;
      else
        info(t2).fixupStack(-info($1).opSize());
    }
    if (allow) {
      if ($0.hasStackdepth && !t.hasStackdepth) t.stackdepth = $0.stackdepth;
      if ($0.to == info($1).outOp())
        $SUBST(t);
      else
        $SUBST(t, t2);
    }
  `));
  // moved the sfree up too far!
  mixin(opt("load_address_into_sourcer", `^LoadAddress, ^SFree, *:
    info($2).hasIndirect(0, $0.to) && info($2).opSize() > 1
    =>
    $T t = $2.dup;
    info(t).setIndirect(0, $0.to, $0.from);
    $T t2 = $0;
    if (info($2).growsStack)   info(t2).fixupStack( info($2).opSize());
    if (info($2).shrinksStack) info(t2).fixupStack(-info($2).opSize());
    $SUBST(t, t2, $1);
  `));
  mixin(opt("store_into_pop", `*, ^Pop:
    info($0).numInOps() == 0 && info($0).outOp().isIndirect(0) == "%esp" && info($0).opSize == $1.size
    && $0.kind != $TK.FPIntPop /or/ $TK.FPLongPop /* doesn't take register argument */
    =>
    $T t1;
    t1.kind = $TK.SFree;
    t1.size = info($0).opSize;
    $T t2 = $0.dup;
    // don't need to fix up t's sources; no op can freely both read and write from memory
    // do need to fix up dest though
    auto dest = $1.dest;
    dest.fixupString(-t1.size);
    info(t2).outOp = dest;
    bool block = false;
    if ($0.kind == $TK.SSEOp) {
      block = true;
      int offs;
      if ($1.hasStackdepth && $1.dest.isIndirect2(offs) == "%esp" && ($1.stackdepth - offs) % 16 == 0)
        block = false;
      // else logln("fail2 @", $0);
    }
    if (!block) $SUBST(t1, t2);
  `));
  // FP small fry
  mixin(opt("float_fold_redundant_save_load", `^FloatPop || ^DoublePop, ^FloatLoad || ^DoubleLoad:
    $0.dest == $1.source && info($0).opSize == info($1).opSize
    =>
    $T t;
    if ($0.kind == $TK.FloatPop) t.kind = $TK.FloatStore;
    else t.kind = $TK.DoubleStore;
    t.dest = $0.dest;
    $SUBST(t);
  `));
  /*mixin(opt("comm_switch", `^MathOp, ^Mov, ^MathOp:
    $0.opName.isCommutative() && $0.op1 == $1.to && $1.from == $0.op2
    && $2.op1.isNumLiteral() && $2.op2 == $1.to
    =>
    $T t0 = $0; swap(t0.op1, t0.op2);
    $T t1 = $1; swap(t1.from, t1.to);
    $SUBST(t0, t1, $2);
  `));*/
  mixin(opt("fold_adds", `^MathOp, ^MathOp:
    $0.opName == "addl" && $1.opName == "addl" && $0.op2 == $1.op2 && $0.op2.isUtilityRegister() &&
    $0.op1.isNumLiteral() && $1.op1.isNumLiteral()
    =>
    $T t = $0;
    t.op1 = qformat("$"[], $0.op1.literalToInt() + $1.op1.literalToInt());
    if (t.op1 != "$0") $SUBST(t);
    else $SUBST();
  `));
  mixin(opt("const_subl_as_addl", `^MathOp:
    $0.opName == "subl" && $0.op1.isNumLiteral()
    =>
    $T t = $0;
    t.opName = "addl";
    t.op1 = qformat("$", -literalToInt(t.op1));
    $SUBST(t);
  `));
  mixin(opt("push_temp_into_load", `^Push, *:
    $0.size == info($1).opSize &&
    info($1).hasIndirectSrc(0, "%esp") &&
   !info($1).resizesStack() &&
    info($1).outOp().isIndirect() != "%esp" &&
   !info($0).opContains(info($1).outOp()) &&
    $1.kind != $TK.FloatIntLoad /* can't do mem loads :( */ &&
    $1.kind != $TK.LoadAddress /* lel */ &&
    // flds needs memory source
   ($1.kind != $TK.FloatLoad || !$0.source.isUtilityRegister() && !$0.source.isNumLiteral()) &&
   // fcmps must not literal
   ($1.kind != $TK.FloatCompare || !$0.source.isNumLiteral()) &&
   // idivl likewise
   ($1.kind != $TK.ExtendDivide || !$0.source.isNumLiteral())
    =>
    $T t = $1;
    if (t.hasStackdepth()) t.stackdepth -= $0.size;
    info(t).setIndirectSrc(0, "%esp", $0.source);
    bool block;
    if (t.kind == $TK.SSEOp) { // alignment!!
      int offs;
      block = true;
      if ($0.hasStackdepth() && $0.source.isIndirect2(offs) == "%esp" && ($0.stackdepth - offs) % 16 == 0)
        block = false;
      // else logln("fail @", $0);
    }
    if (!block) $SUBST(t, $0);
  `));
  mixin(opt("store_float_into_double", `^FloatPop || ^FloatStore, ^DoublePop || ^DoubleStore:
    ($0.dest == "(%esp)" || $0.dest == "4(%esp)") && $1.dest == "(%esp)"
    =>
    $SUBST($1);
  `));
  mixin(opt("pop_into_far_load", `^FloatPop || ^DoublePop, ^FloatLoad || ^DoubleLoad, ^FloatLoad || ^DoubleLoad:
    info($0).opSize() == info($1).opSize() &&
    info($0).opSize() == info($2).opSize() &&
    $0.dest == $2.source
    =>
    $T t = $0.dup;
    t.kind = $TK.FloatStore;
    $T t2;
    t2.kind = $TK.PureFloat;
    t2.opName = "fxch";
    $SUBST(t, $1, t2);
  `));
  // nvm opts
  mixin(opt("nevermind_up", `*, ^Nevermind:
    $0.kind != $TK.Nevermind && !info($0).opContains($1.dest) &&
    $0.kind != $TK.SAlloc /or/ $TK.SFree /or/ $TK.Label /or/ $TK.Jump /or/ $TK.Call
    =>
    $SUBST($1, $0);
  `));
  mixin(opt("matching_nvms", `^Nevermind, ^Nevermind:
    $0.dest == $1.dest => $SUBST($0);
  `));
  // movaps foo, (%esp); movaps (%esp), bar; [sfree 16]
  mixin(opt("pointless_store", `^SSEOp, ^SSEOp, *:
    $0.opName == "movaps" && $1.opName == "movaps" &&
    $0.op2 == $1.op1 && $0.op2 == "(%esp)"
    =>
    bool freesIt = $2.kind == $TK.SFree && $2.size >= 16;
    if ($0.op1 == $1.op2) { // foo == bar
      if (freesIt) $SUBST($2);
      else $SUBST($0, $2);
    } else { // foo != bar
      if (freesIt) {
        $T t = $0;
        t.op2 = $1.op2;
        $SUBST($2, t);
      } else {
        $T t = $1;
        t.op1 = $0.op1;
        $SUBST($0, t, $2);
      }
    }
  `));
  mixin(opt("pointless_push", `^Push, ^SFree:
    $0.size <= $1.size
    =>
    auto rest = $1.size - $0.size;
    if (rest) {
      $T t = $1.dup;
      t.size = rest;
      $SUBST(t);
    } else $SUBST();
  `));
  
  mixin(opt("push_move_back_to_store", `^Push, ^Mov || ^Mov2 || ^Mov1:
    $0.size == info($1).opSize() &&
    $1.from == "(%esp)" && $1.to == $0.source
    =>
    $SUBST($0);
  `));
  /*mixin(opt("shufps_direct", `^SSEOp, ^SSEOp, ^SSEOp:
    $0.opName == "movaps" && $2.opName == "movaps" &&
    $1.opName.startsWith("shufps") &&
    $0.op2 == $2.op1 && $0.op2 == $1.op1 && $0.op2 == $1.op2 &&
    $2.op2.isSSERegister()
    =>
    $T t1 = $0;
    t1.op2 = $2.op2;
    $T t2 = $1;
    t2.op1 = t1.op2;
    t2.op2 = t1.op2;
    $SUBST(t1, t2);
  `));*/
  // lel
  mixin(opt("sse_lel1", `^SSEOp, ^SSEOp:
    $0.opName == "movaps" && $1.opName == "movaps" &&
    $0.op2 == "(%esp)"
    =>
    int offs;
    if (($1.op1.isIndirect2(offs) == "%esp" && offs || $1.op1.isSSERegister() && $1.op2.isSSERegister()) && $1.op2 != $0.op1) {
      $SUBST($1, $0);
    }
  `));
  // movaps A -> C; movaps B -> D; mulps D, C; movaps C, R;  R != B || A == B
  // => movaps A -> R; mulps B, R
  mixin(opt("sse_lel2", `^SSEOp, ^SSEOp, ^SSEOp, ^SSEOp:
    $0.opName == "movaps" && $1.opName == "movaps" && $2.opName.isSSEMathOp() && $3.opName == "movaps" &&
    $2.op1 == $1.op2 && $2.op2 == $0.op2 && $2.op2 == $3.op1 && $3.op2.isSSERegister() &&
    ($3.op2 != $1.op1 || $1.op1 == $0.op1)
    =>
    $T t1 = $0, t2 = $2;
    t1.op2 = $3.op2;
    t2.op1 = $1.op1;
    t2.op2 = t1.op2;
    $SUBST(t1, t2);
  `));
  mixin(opt("sse_remove_nop", `^SSEOp: $0.opName == "movaps" && $0.op1 == $0.op2 => $SUBST(); `));
  
  // It's complicated. Just trust me, I did the math.
  mixin(opt("complicated", `^Push, ^Pop:
    $0.size == 4 && $1.size == 4 &&
    $1.dest == "4(%esp)" && $0.source != "(%esp)"
    =>
    if ($0.source.isMemRef()) {
      $T t1;
      t1.kind = $TK.SFree;
      t1.size = 4;
      $T t2 = $0.dup;
      info(t2).fixupStack(-4);
      $SUBST(t1, t2);
    } else {
      $T t;
      t.kind = $TK.Mov;
      t.from = $0.source;
      t.to = "(%esp)";
      $SUBST(t);
    }
  `));
  // common with doubles
  mixin(opt("direct_double_store", `^DoubleStore || ^DoublePop, ^Pop, ^Pop:
    $0.dest == "(%esp)" &&
    $1.size == 4 && $1.dest.isIndirect() == "%esp" &&
    $2.size == 4 && $2.dest == $1.dest
    =>
    $T t0 = $0.dup;
    t0.dest = $1.dest;
    $T t1;
    t1.kind = $TK.SFree;
    t1.size = 8;
    $SUBST(t0, t1);
  `));
  mixin(opt("direct_double_load", `^Push, ^Push, ^DoubleLoad:
    $0.size == 4 && $0.source.isIndirect() == "%esp" &&
    $1.size == 4 && $1.source == $0.source &&
    $2.source == "(%esp)"
    =>
    int o0;
    $0.source.isIndirect2(o0);
    $T t0 = $2.dup;
    t0.source = qformat(o0-4, "(%esp)");
    $T t1;
    t1.kind = $TK.SAlloc;
    t1.size = 8;
    // probably not needed but make sure for correctness sake.
    // if unnecessary, sfree will get rid of it.
    $T t2;
    t2.kind = $TK.DoubleStore;
    t2.dest = "(%esp)";
    $SUBST(t0, t1, t2);
  `));
  bool sequal(string[] str...) {
    foreach (s; str[1..$]) if (s != str[0]) return false;
    return true;
  }
  bool iequal(int[] ints...) {
    foreach (i; ints[1..$]) if (i != ints[0]) return false;
    return true;
  }
  bool popchain(Transaction[] trs...) {
    if (trs[0].dest.isIndirect() == "%esp") {
      foreach (tr; trs[1..$]) if (tr.dest != trs[0].dest || tr.size != trs[0].size) return false;
    } else { // steps of four
      int offs1, offs2;
      foreach (i, tr; trs[1..$]) if (tr.dest.isIndirect2(offs2) != trs[0].dest.isIndirect2(offs1) || offs2 != offs1 + (i + 1) * trs[0].size || tr.size != trs[0].size) return false;
    }
    return true;
  }
  bool pushequal(Transaction[] trs...) {
    foreach (tr; trs[1..$]) if (tr.source != trs[0].source || tr.size != trs[0].size) return false;
    return true;
  }
  mixin(opt("known_aligned_push_into_load", `^Push, ^Push, ^Push, ^Push, ^SSEOp:
    pushequal($0, $1, $2, $3) && $4.opName == "movaps"[] /or/ "cvtdq2ps"[] && $4.op1 == "(%esp)" && $4.op2.isSSERegister()
    =>
    int offs;
    if ($0.source.isIndirect2(offs) == "%esp" && (offs -= 12, true)) {
      $T t = $4.dup;
      // can't rely on alignment!
      if (t.opName == "movaps")
        t.opName = "movups";
      t.op1 = qformat(offs, "(%esp)"[]);
      $SUBST(t, $0, $1, $2, $3);
    }
  `));
  mixin(opt("push_after_unpack", `^Push, ^SSEOp: $1.opName == "punpckldq" && $1.op1.isSSERegister() && $1.op2.isSSERegister() => $SUBST($1, $0); `));
  mixin(opt("push_or_mov_before_movaps", `^Push, ^SSEOp || ^MovD:
    (
      $1.kind == $TK.SSEOp && $1.opName == "movaps" && $1.op2.isSSERegister() ||
      $1.kind == $TK.MovD && $1.to.isSSERegister() && $1.from.isIndirect() != "%esp"
    )
    =>
    int offs;
    if ($1.kind == $TK.SSEOp && $1.op1.isIndirect2(offs) == "%esp" && offs >= $0.size) {
      $T t = $1;
      info(t).fixupStack(-$0.size);
      $SUBST(t, $0);
    }
    else if ($1.kind == $TK.MovD) $SUBST($1, $0);
  `));
  mixin(opt("convert_push_into_sse_fragment_load", `^Push, ^Push, ^MovD, ^SSEOp, ^MovD, ^SFree:
    $0.size == 4 && $1.size == 4 && 
    $2.from == "4(%esp)" && $2.to.isSSERegister() &&
    $3.opName == "punpckldq" &&
    $4.from == "(%esp)" && $4.to.isSSERegister() &&
    $5.size == 8
    =>
    $T t1 = $2.dup, t2 = $3.dup, t3 = $4.dup;
    t1.from = $0.source;
    t3.from = $1.source;
    $SUBST(t1, t2, t3);
  `));
  mixin(opt("dense_address_form", `^LoadAddress, ^MathOp:
    $0.from.isIndirect() == "%esp" && $1.opName == "addl" && $0.to == $1.op2 && $1.op1.isUtilityRegister()
    =>
    $T t = $0;
    int offs;
    $0.from.isIndirect2(offs);
    t.from = qformat(offs, "(%esp,"[], $1.op1, ")"[]);
    $SUBST(t);
  `));
  string pfpsource(Transaction* t) {
    with (Transaction.Kind) switch (t.kind) {
      case Push, FloatLoad: return t.source;
      case Pop: return t.dest;
      case SSEOp: return t.op1;
      default: fail;
    }
  }
  string pfpsetsource(Transaction* t, string s) {
    with (Transaction.Kind) switch (t.kind) {
      case Push, FloatLoad: return t.source = s;
      case Pop: return t.dest = s;
      case SSEOp: return t.op1 = s;
      default: fail;
    }
  }
  mixin(opt("dense_address_form2", `^MathOp, ^Push || ^Pop || ^SSEOp || ^FloatLoad:
    $0.opName == "addl" && pfpsource(&$1).isIndirect() == $0.op2 &&
    ($0.op1.isUtilityRegister() || $0.op1.isNumLiteral())
    =>
    $T t = $1;
    int offs;
    pfpsource(&$1).isIndirect2(offs);
    string newsource;
    if ($0.op1.isUtilityRegister())
      newsource = qformat(offs, "("[], $0.op2, ","[], $0.op1, ")"[]);
    else
      newsource = qformat(offs + $0.op1.literalToInt(), "("[], $0.op2, ")"[]);
    pfpsetsource(&t, newsource);
    $SUBST(t, $0);
  `));
  mixin(opt("movaps_pointless_read", `^SSEOp, ^SSEOp:
    $0.opName == "movaps"[] /or/ "movups"[] && $1.opName == "movaps"[] /or/ "movups"[]
    && $0.op2 == $1.op1
    && $0.op1.isSSERegister() && $1.op2.isSSERegister()
    =>
    auto t2 = $1.dup;
    t2.op1 = $0.op1;
    auto t0 = $0;
    if ($1.opName == "movaps") t0.opName = "movaps"; // we know it's aligned
    if (t2.op1 == t2.op2) $SUBST(t0);
    else $SUBST(t0, t2);
  `));
  mixin(opt("denser_address_form", `^MathOp, ^Push || ^FloatLoad || ^Pop:
    ($0.opName == "imull" || $0.opName == "shl") && $0.op1.isNumLiteral() &&
    pfpsource(&$1).isIndirect().contains($0.op2)
    =>
    $T t = $1;
    int offs;
    auto regs = pfpsource(&t).isIndirect2(offs);
    int mul = $0.op1.literalToInt();
    // mul = 2 ^ shl
    if ($0.opName == "shl") { int mul2 = 1; while (mul--) mul2 *= 2; mul = mul2; }
    if (mul == 1 /or/ 2 /or/ 4 /or/ 8) {
      pfpsetsource(&t, qformat(offs, "("[], regs, ","[], mul, ")"[]));
      $SUBST(t, $0);
    }
  `));
  mixin(opt("shlimull", `^MathOp:
    $0.opName == "imull" && $0.op1.isNumLiteral() && $0.op1.literalToInt() == 2 /or/ 4 /or/ 8 /or/ 16 /or/ 32 /or/ 64 /or/ 128 /or/ 256
    =>
    int shf;
    // suboptimal but meh.
    // feel free to write up a clever algo here.
    switch ($0.op1.literalToInt()) {
      case 2: shf = 1; break;
      case 4: shf = 2; break;
      case 8: shf = 3; break;
      case 16: shf = 4; break;
      case 32: shf = 5; break;
      case 64: shf = 6; break;
      case 128: shf = 7; break;
      case 256: shf = 8; break;
    }
    $T t = $0;
    t.opName = "shll";
    t.op1 = qformat("$", shf);
    $SUBST(t);
  `));
  // Muda!
  /*mixin(opt("denser_address_form_2", `^Mov, ^MathOp, ^Mov, ^MathOp:
    $0.to.isUtilityRegister() && $2.to.isUtilityRegister() &&
    $1.opName == "imull" && $3.opName == "addl" &&
    $0.to == $1.op2 && $2.to == $3.op2 && $1.op2 == $3.op1 &&
    $1.op1.isNumLiteral() && $1.op1.literalToInt() == 2 /or/ 4 /or/ 8
    =>
    $T t;
    t.kind = $TK.LoadAddress;
    t.from = qformat("("[], $0.to, ","[], $2.to, ","[], $1.op1.literalToInt(), ")"[]);
    t.to = $3.op2;
    $SUBST($0, $2, t);
  `));*/
  mixin(opt("lea_mov_into_push_pop", `^LoadAddress, ^Mov, ^Push || ^Pop || ^FloatLoad:
    $0.from.isIndirect() == "%esp" &&
    pfpsource(&$2).isIndirect().startsWith(qformat($0.to, ","[], $1.to))
    =>
    $T t = $2;
    int offs1, offs2;
    pfpsource(&t).isIndirect2(offs1);
    $0.from.isIndirect2(offs2);
    auto rest = pfpsource(&$2).isIndirect().startsWith(qformat($0.to, ","[], $1.to));
    int combined_offset = offs1 + offs2;
    pfpsetsource(&t, qformat(combined_offset, "(%esp,"[], $1.to, rest, ")"[]));
    $SUBST($1, t);
  `));
  mixin(opt("rename_earlier", `^MathOp, ^Mov, ^Mov || ^LoadAddress:
    $0.op1.isNumLiteral() && $1.from == $0.op2 && $1.to.isUtilityRegister() && $2.to == $1.from
    =>
    $T t1 = $1, t2 = $0;
    t2.op2 = t1.to;
    $SUBST(t1, t2, $2);
  `));
  mixin(opt("rename_step2", `*, ^Mov, ^MathOp, ^Mov:
    $2.op2 == $1.to && $1.from == info($0).outOp() && !info($0).opContainsSrc($1.from) && $3.to == $1.from && $3.from.isIndirect() == "%esp"
    =>
    $T t = $0;
    info(t).outOp = $1.to;
    $SUBST(t, $2, $3);
  `));
  mixin(opt("pop_sooner", `^Mov || ^MathOp, ^Pop:
    $1.dest.isUtilityRegister() && $0.kind != $TK.Push && !pinsRegister($0, $1.dest) && info($0).couldFixup(-$1.size) &&
    $0.from.isIndirect() != "%ebp" && !$0.to.isIndirect() /* unsafe for push/pop */
    =>
    $T t = $0.dup;
    info(t).fixupStack(-$1.size);
    $SUBST($1, t);
  `));
  mixin(opt("move_literal_downwards", `^Mov, *:
    ($1.kind != $TK.SSEOp) &&
    ($1.kind != $TK.Mov || !$1.from.isLiteral() || $1.from.isNumLiteral()) &&
    $0.from.isLiteral() && !$0.from.isNumLiteral() && $0.to.isIndirect() == "%esp" &&
    !pinsRegister($1, $0.to) &&
    info($0).couldFixup(info($1).stackchange)
    =>
    $T t = $0.dup;
    info(t).fixupStack(info($1).stackchange);
    $SUBST($1, t);
  `));
  mixin(opt("remove_slightly_stupid_push_pop_pair", `^Push, ^Mov, ^Pop:
    $0.size == $2.size && $0.size == 4 &&
    $1.to.isRegister() && $1.from != "(%esp)" &&
    $2.dest.isRegister() && $2.dest != $1.to &&
    !info($1).opContains($2.dest)
    =>
    $T t1, t2;
    t1.kind = $TK.Mov;
    t1.from = $0.source;
    t1.to = $2.dest;
    t2 = $1.dup;
    info(t2).fixupStack(-4);
    $SUBST([t1, t2]);
  `));
  // lol
  mixin(opt("hyperspecific_pop_chain", `^Pop, ^Pop, ^Pop, ^Pop, ^Pop, ^Pop, ^Pop, ^Pop:
    sequal($0.dest, $1.dest, $2.dest, $3.dest) &&
    sequal($4.dest, $5.dest, $6.dest, $7.dest) &&
    iequal($0.size, $1.size, $2.size, $3.size, $4.size, $5.size, $6.size, $7.size) &&
    $0.size == 4 &&
    $0.dest == "16(%esp)"
    =>
    $T t1 = $4.dup, t2 = $5.dup, t3 = $6.dup, t4 = $7.dup;
    info(t1).fixupStack(16);
    info(t2).fixupStack(16);
    info(t3).fixupStack(16);
    info(t4).fixupStack(16);
    $T t5;
    t5.kind = $TK.SFree;
    t5.size = 16;
    $SUBST(t1, t2, t3, t4, t5);
  `));
  mixin(opt("pointless_mov", `^Mov, ^Pop:
    $0.to == "(%esp)" && $1.size == 4 && $1.dest == $0.from
    =>
    $T t;
    t.kind = $TK.SFree;
    t.size = 4;
    $SUBST(t);
  `));
  mixin(opt("double_load_into_math", `^FloatLoad, ^FloatLoad, ^FloatMath:
    $0.source == $1.source && !$2.floatSelf
    =>
    $T t = $2.dup;
    t.floatSelf = true;
    $SUBST($0, t);
  `));
  mixin(opt("silly_lea", `^LoadAddress, ^FloatLoad:
    $0.from.isIndirect() == "%esp" && $0.to.isUtilityRegister() && 
    $1.source.isIndirect() == $0.to
    =>
    $T t = $1;
    int offs1, offs2;
    $0.from.isIndirect2(offs1);
    t.source.isIndirect2(offs2);
    t.source = qformat(offs1 + offs2, "(%esp)"[]);
    $SUBST(t, $0);
  `));
  mixin(opt("movaps_later", `^SSEOp, *:
    $0.opName == "movaps" && $0.op1.isSSERegister() && $0.op2 == "(%esp)" &&
    $1.kind != $TK.Push /or/ $TK.Pop && !info($1).opContains($0.op1)
    =>
     if (info($1).couldFixup(-16))
      $SUBST($1, $0);
  `));
  mixin(opt("movaps_and_pop_to_direct", `^SSEOp, ^Pop, ^Pop, ^Pop, ^Pop:
    $0.opName == "movaps" && $0.op1.isSSERegister() && $0.op2 == "(%esp)" &&
    popchain($1, $2, $3, $4) && $1.size == 4
    =>
    $T t1, t2 = $0.dup;
    t1.kind = $TK.SFree;
    t1.size = 16;
    t2.op2 = $1.dest;
    int offs;
    // must be guaranteed aligned!
    if (t2.op2.isIndirect2(offs) != "%esp" || (offs % 16) != 0)
      t2.opName = "movups";
    $SUBST(t2, t1);
  `));
  mixin(opt("simplify_pure_sse_math_opers", `^SSEOp, ^SSEOp, ^SSEOp:
    $0.opName == "movaps" && $0.op1.isSSERegister() &&
    $1.opName == "addps"[] /or/ "subps"[] /or/ "mulps"[] /or/ "divps"[] &&
    $1.op1 != $1.op2 &&
    $1.op2 == $0.op2 &&
    $2.opName == "movaps" && $2.op2.isSSERegister() &&
    $2.op2 == $0.op1 && $2.op1 == $0.op2
    =>
    $T t = $1;
    t.op2 = $0.op1;
    $SUBST(t, $0);
  `));
  mixin(opt("small_fry_1", `^MathOp, ^Pop:
    $1.size == 4 && $0.op1.isNumLiteral() && $0.op2 == "(%esp)"
    =>
    $T t = $0.dup;
    t.op2 = $1.dest;
    info(t).fixupStack(-4);
    $SUBST($1, t);
  `));
  mixin(opt("direct_push_after_mov", `^Push, ^Mov:
    !$0.source.isMemAccess() && info($1).couldFixup(-$0.size) &&
    !info($1).opContains("%ebp") && $1.to.find($0.source) == -1 &&
    (!$1.from.isLiteral() || $1.from.isNumLiteral()) /* prevent loop with move_literal_downwards */
    =>
    $T t = $1.dup;
    info(t).fixupStack(-$0.size);
    $SUBST(t, $0);
  `));
  mixin(opt("faster_vector_move", `^Push, ^Push, ^Push, ^Push, ^Pop, ^Pop, ^Pop, ^Pop, ^SFree:
    $0.size==4&&$1.size==4&&$2.size==4&&$3.size==4&&$4.size==4&&$5.size==4&&$6.size==4&&$7.size==4&&
    $8.size == 16 &&
    ($0.source == "$""0" && $1.source == "16(%esp)" && $2.source == "16(%esp)" && $3.source == "16(%esp)"
   ||$0.source == "12(%esp)" && $1.source == "12(%esp)" && $2.source == "12(%esp)" && $3.source == "12(%esp)") &&
    $4.dest == "32(%esp)" && $5.dest == "32(%esp)" && $6.dest == "32(%esp)" && $7.dest == "32(%esp)"
    =>
    if ($0.source == "$""0") {
      $T t1;
      t1.kind = $TK.SFree;
      t1.size = 4;
      $T t2;
      t2.kind = $TK.Pop;
      t2.dest = "12(%esp)";
      t2.size = 12;
      $T t3;
      t3.kind = $TK.Mov;
      t3.from = "$""0";
      t3.to = "16(%esp)";
      $SUBST(t1, t2, t3);
    } else {
      $T t;
      t.kind = $TK.Pop;
      t.dest = "16(%esp)";
      t.size = 16;
      $SUBST(t);
    }
  `));
  
  mixin(opt("value_push_after_compare", `^Push, ^Compare:
    $0.source.isNumLiteral() && $1.op1.isRegister() && $1.op2.isRegister()
    => $SUBST($1.dup, $0.dup);
  `));
  // push foo, pop (%esp) => sfree 4; push foo
  bool remove_stack_push_pop_chain(Transcache cache, ref int[string] labels_refcount) {
    int sz;
    string firstAddr, secondAddr;
    bool hasSfree;
    int sfreeBias, postFree;
    auto match = cache.findMatch("remove_stack_push_pop_chain", delegate int(Transaction[] list) {
      // erase remnants of earlier iteration!
      sz = 0;
      firstAddr = secondAddr = null;
      hasSfree = false;
      sfreeBias = postFree = 0;
      if (list.length < 2) return false;
      int marker = -1, marker2 = -1;
      foreach (i, entry; list)
        if (entry.kind != Transaction.Kind.Push) { marker = i; break; }
      if (!marker || marker == -1) return false;
      foreach (i, entry; list[marker .. $])
        if (entry.kind != Transaction.Kind.Pop) { marker2 = marker + i; break; }
      if (marker2 == -1) marker2 = list.length;
      if (marker2 != marker * 2)
        return false;
      if (list.length > marker2 && list[marker2].kind == Transaction.Kind.SFree) {
        hasSfree = true;
        sfreeBias = list[marker2].size;
      }
      string curAddr;
      foreach (entry; list[0 .. marker]) {
        // if (entry.source.isIndirect() != "%esp") return false;
        if (!firstAddr) {
          if (!entry.source.isIndirect()) return false;
          curAddr = firstAddr = entry.source;
        } else if (entry.source != curAddr) return false;
        int loffs;
        string lindir = curAddr.isIndirect2(loffs);
        if (lindir != "%esp")
          if (loffs - 4) curAddr = qformat(loffs - 4, "("[], lindir, ")"[]);
          else curAddr = qformat("("[], lindir, ")"[]);
      }
      foreach (entry; list[marker .. marker2]) {
        if (entry.dest.isIndirect() != "%esp") return false;
        if (!secondAddr) secondAddr = entry.dest;
        else if (entry.dest != secondAddr) return false;
      }
      
      sz = marker * 4;
      
      int offs;
      if (secondAddr.isIndirect2(offs) && sz + sfreeBias > offs) {
        // sfree eats into our pop target. be careful, ignore sfree.
        sfreeBias = 0;
        hasSfree = false;
      }
      
      if (firstAddr.isIndirect2(offs) == "%esp" && offs < marker * 4 + sfreeBias)
        return false; // too close to home
      int offs2; secondAddr.isIndirect2(offs2);
      offs2 -= sz;
      if (offs2 < 0) {
        logln("firstAddr ", firstAddr, ", secondAddr ", secondAddr);
        fail;
      }
      if (offs2 > sfreeBias) return false;
      
      postFree = offs2; // sz already subtracted
      if (sfreeBias - postFree < 0) {
        logln("sfreeBias ", sfreeBias, ", postFree ", postFree, ", sz ", sz, ", ops ", list);
        fail;
      }
      
      return marker * 2 + hasSfree;
    });
    bool changed;
    if (match.length) do {
      if (xpar != -1 && si >= xpar) continue;
      si ++;
      
      Transaction t1;
      t1.kind = Transaction.Kind.SFree;
      t1.size = sz + postFree;
      Transaction t2;
      t2.kind = Transaction.Kind.Push;
      
      int offs;
      auto relTo = firstAddr.isIndirect2(offs);
      if (relTo == "%esp") {
        t2.source = qformat(offs + 4 - 2 * sz - postFree, "(%esp)"[]);
      } else {
        t2.source = qformat(offs + 4 - sz, "("[], relTo, ")"[]);
      }
      t2.size = sz;
      
      if (postFree) {
        Transaction t3;
        t3.kind = Transaction.Kind.SFree;
        t3.size = sfreeBias - postFree;
        match.replaceWith(t1, t2, t3);
      } else {
        match.replaceWith(t1, t2);
      }
      changed = true;
    } while (match.advance());
    return changed;
  }
  opts ~= stuple(&remove_stack_push_pop_chain, "remove_stack_push_pop_chain", true, false);
  // can't be sure we're actually at the end since 1024 flushes now
  // mixin(opt("remove_closing_leas", `^LoadAddress, ] => $SUBST();`));
  mixin(opt("earlier_stackload", `^MathOp, ^Mov:
    $1.from == "(%esp)" && $1.to.isUtilityRegister() && !info($0).opContains($1.to) && !info($0).opContains($1.from)
    =>
    $SUBST($1, $0);
  `));
  mixin(opt("math_into_ref", `^MathOp, ^Mov:
    $0.op1.isNumLiteral() && $0.op2.isUtilityRegister() && $0.opName == "addl" &&
    $1.from.isIndirect() == $0.op2
    =>
    $T t1 = $1;
    int indir; $1.from.isIndirect2(indir);
    indir += $0.op1.literalToInt();
    t1.from = qformat(indir, "("[], $0.op2, ")"[]);
    if (t1.to == $0.op2) $SUBST(t1); // overwrite target, no need to keep the math
    else if (t1.to.contains($0.op2)) { } // confusing
    else $SUBST(t1, $0); // keep the math
  `));
  mixin(opt("move_lea_after_unrelated_op", `^LoadAddress, (^Pop || ^Mov):
    $0.to.isUtilityRegister() && !info($1).opContains($0.to) && !info($0).opContains(($1.kind == $TK.Pop)?$1.dest:$1.to)
    =>
    $T t = $0;
    if ($1.kind == $TK.Pop && t.hasStackdepth) t.stackdepth -= $1.size;
    $SUBST($1, t);
  `));
  // this sequence would leave the target register pointing at an invalid area of the stack
  // ergo it must be bogus
  mixin(opt("sfree_cancels_lea", `^LoadAddress, ^SFree:
    $0.from == "(%esp)" && $1.size
    =>
    $SUBST($1);
  `));
  mixin(opt("break_up_push_pop", `^Push || ^Pop:
    $0.size > 4 && ($0.size % 4) == 0 && $0.size <= 64 // just gets ridiculous beyond that point 
    =>
    auto sz = $0.size;
    $T[] res;
    $T cur = $0;
    cur.size = 4;
    int offs;
    string* op;
    if ($0.kind == $TK.Push) op = &cur.source;
    else op = &cur.dest;
    auto indir = (*op).isIndirect2(offs, true);
    // Try to pry apart the subtle weave of if clauses.
    // Just try.
    // I dare you.
    if ($0.kind == $TK.Push) {
      if (indir) offs = offs + $0.size - 4;
    }
    if (indir) cur.source = qformat(offs, "("[], indir, ")"[]);
    if (indir == "%esp") indir = null;
    for (int i = 0; i < sz; i += 4) {
      if (indir) *op = qformat(offs, "("[], indir, ")"[]);
      res ~= cur;
      if ($0.kind == $TK.Push) { offs -= 4; if (cur.hasStackdepth) cur.stackdepth += 4; }
      else { offs += 4; if (cur.hasStackdepth) cur.stackdepth -= 4; }
    }
    $SUBST(res);
  `));
  bool lookahead_remove_redundants(Transcache cache, ref int[string] labels_refcount) {
    bool changed, pushMode; int pushSize;
    auto match = cache.findMatch("lookahead_remove_redundants", delegate int(Transaction[] list) {
      if (list.length <= 1) return false;
      auto head = list[0];
      string check;
      with (Transaction.Kind) {
        if (head.kind == Mov || head.kind == LoadAddress) check = head.to;
        if (head.kind == FloatStore ) check = head.dest;
        if (head.kind == DoubleStore) check = head.dest;
        if (head.kind == MathOp) check = head.op2;
        pushMode = false;
        if (head.kind == Push) { pushMode = true; check = "(%esp)"; pushSize = head.size; }
        if (head.kind == SSEOp && head.opName == "movaps" && (
          head.op2.isSSERegister() || head.op2 == "(%esp)")) check = head.op2;
      }
      
      if (!check) return false;
      if (!check.isUtilityRegister() && !check.isSSERegister() && check != "(%esp)") return false;
      
      bool hasStackDependence(string s) {
        if (s.find("%esp") != -1) return true;
        int offs;
        if (s.isIndirect2(offs) == "%ebp") return offs < 0;
        return false;
      }
      
      bool unneeded;
      int i;
      bool test(string s) {
        if (s.find(check) != -1) return true;
        if (check == "(%esp)" && hasStackDependence(s)) return true;
        if (check.find("%eax") != -1 && (s.find("%ax") != -1 || s.find("%al") != -1) || s.find("%ah") != -1) return true;
        if (check.find("%ebx") != -1 && (s.find("%bx") != -1 || s.find("%bl") != -1) || s.find("%bh") != -1) return true;
        if (check.find("%ecx") != -1 && (s.find("%cx") != -1 || s.find("%cl") != -1) || s.find("%ch") != -1) return true;
        if (check.find("%edx") != -1 && (s.find("%dx") != -1 || s.find("%dl") != -1) || s.find("%dh") != -1) return true;
        return false;
      }
      outer:foreach (_i, entry; list[1 .. $]) {
        i = _i;
        with (Transaction.Kind) switch (entry.kind) {
          case SFree:
            if (check == "(%esp)") {
              if (entry.size >= info(head).opSize())
                unneeded = true;
              break outer;
            }
            continue;
          case SAlloc:
            if (check == "(%esp)") break outer;
            continue;
          case Mov2, Mov1, Swap, Text, Extended: break outer; // weird stuff, not worth the confusion
          case PureFloat:
            continue;    // no change
          
          case Jump:
            if (entry.keepRegisters) break outer;
          case Call:
            if (check.isUtilityRegister()) {
              // arguments on the stack (cdecl)
              if (!test(entry.dest))
                unneeded = true;
              break outer;
            }
          case Label:
            if (entry.keepRegisters || check.isSSERegister()) break outer;
            if (check != "(%esp)") unneeded = true;
          case Compare:
            break outer;
          
          case ExtendDivide:
            if (check == "%eax") break outer;
          case Push:
            if (check == "(%esp)") break outer;
          case FloatLoad, DoubleLoad, RealLoad, RegLoad, FloatIntLoad, FloatLongLoad, FloatCompare:
            if (test(entry.source)) break outer;
            continue;
          
          case Pop:
            if (check == "(%esp)") break outer;
          case Nevermind, FloatPop, DoublePop, FPIntPop, FPLongPop, FloatStore, DoubleStore:
            if (entry.dest == check) { unneeded = true; break outer; }
            if (test(entry.dest)) break outer;
            continue;
          
          case FloatMath:
	    if (entry.op1 && test(entry.op1)) break outer;
	    continue;
          case MathOp:
            if (test(entry.op1) || test(entry.op2)) break outer;
            continue;
          
          case Mov, MovD, LoadAddress:
            if (test(entry.from)) break outer;
            if (entry.to == check) {
              unneeded = true;
              break outer;
            }
            if (test(entry.to)) break outer;
            continue;
          
          case SSEOp:
            if (test(entry.op1)) break outer;
            if (entry.op2 == check) { // all SSE ops have the target as the second operand
              // but not all _read_ it!
              if (entry.opName == "movaps"[] /or/ "movups"[])
                unneeded = true;
              break outer;
            }
            if (test(entry.op2)) break outer;
            continue;
          
          default: break;
        }
        logln("huh? ", entry);
        fail;
      }
      if (unneeded) return i + 2;
      return false;
    });
    if (match.length) do {
      if (xpar != -1 && si >= xpar) continue;
      si ++;
      
      if (pushMode) {
        Transaction t;
        t.kind = Transaction.Kind.SAlloc;
        t.size = pushSize;
        match.replaceWith(t, match[][1 .. $]);
      } else {
        match.replaceWith(match[][1 .. $]); // remove
      }
      changed = true;
    } while (match.advance());
    return changed;
  }
  opts ~= stuple(&lookahead_remove_redundants, "lookahead_remove_redundants"[], true, false);
  mixin(opt("finally_push_memref_to_int", `^Push:
    $0.source.find("___xfcc_encodes_") != -1
    =>
    $T t = $0;
    t.source = qformat("$"[], t.source.between("___xfcc_encodes_", "").atoll());
    $SUBST(t);
  `));
  mixin(opt("finally_remove_nvm", `^Nevermind => $SUBST(); `));
  mixin(opt("stack_2push_2pop_free_into_free_2pop_free", `^Push, ^Push, ^Pop, ^Pop, ^SFree:
    $0.size == 4 && $1.size == 4 && $2.size == 4 && $3.size == 4 &&
    $0.source.isIndirect() == "%esp" && $1.source.isIndirect() == "%esp" &&
    $0.source == $1.source
    =>
    int d0; $0.source.isIndirect2(d0);
    auto tofree = d0 - 4;
    if (!tofree) { // right up against the bottom of the stack
      if ($4.size >= 8) {
        $T t2 = $2.dup, t3 = $3.dup;
        info(t2).fixupStack(-8);
        info(t3).fixupStack(-8);
        $T ts;
        ts.kind = $TK.SFree;
        ts.size = $4.size - 8;
        if (ts.size) $SUBST(t2, t3, ts);
        else $SUBST(t2, t3);
      }
    } else {
      if ($4.size >= tofree) {
        $T t0 = $0.dup, t1 = $1.dup, t2 = $2.dup, t3 = $3.dup;
        info(t0).fixupStack(-tofree);
        info(t1).fixupStack(-tofree);
        info(t2).fixupStack(-tofree);
        info(t3).fixupStack(-tofree);
        $T ts;
        ts.kind = $TK.SFree;
        ts.size = tofree;
        $T tr;
        tr.kind = $TK.SFree;
        tr.size = $4.size - tofree;
        if (tr.size) $SUBST(ts, t0, t1, t2, t3, tr);
        else $SUBST(ts, t0, t1, t2, t3);
      }
    }
  `));
  mixin(opt("stack_push_pop_free_into_free_pop_free", `^Push, ^Pop, ^SFree:
    $0.size == 4 && $1.size == 4 &&
    $0.source.isIndirect() == "%esp"
    =>
    int d0; $0.source.isIndirect2(d0);
    auto tofree = d0;
    if (!tofree) {
      if ($2.size >= 4) {
        $T t1 = $1.dup;
        info(t1).fixupStack(-4);
        $T ts;
        ts.kind = $TK.SFree;
        ts.size = $2.size - 4;
        if (ts.size) $SUBST(t1, ts);
        else $SUBST(t1);
      }
    } else {
      if ($2.size >= tofree) {
        $T t0 = $0.dup, t1 = $1.dup;
        info(t0).fixupStack(-tofree);
        info(t1).fixupStack(-tofree);
        $T ts;
        ts.kind = $TK.SFree;
        ts.size = tofree;
        $T tr;
        tr.kind = $TK.SFree;
        tr.size = $2.size - tofree;
        if (tr.size) $SUBST(ts, t0, t1, tr);
        else $SUBST(ts, t0, t1);
      }
    }
  `));
  mixin(opt("stack_2push_2pop_resort", `^Push, ^Push, ^Pop, ^Pop:
    $0.size == 4 && $1.size == 4 && $2.size == 4 && $3.size == 4 &&
    $0.source == "4(%esp)" && $1.source == "4(%esp)"
    =>
    auto t2 = $2.dup, t1 = $1.dup;
    info(t1).fixupStack(-4);
    info(t2).fixupStack(-4);
    $SUBST($0, $3, t1, t2);
  `));
  mixin(opt("push_pop_into_edi_mov", `barrier: ^Push, ^Pop:
    $0.size == 4 && $1.size == 4 && $0.source.isIndirect() == "%esp" && $1.dest.isIndirect() == "%esp"
    =>
    $T t1;
    t1.kind = $TK.Mov;
    t1.from = $0.source;
    t1.to = "%edi";
    t1.stackdepth = $0.stackdepth;
    $T t2;
    t2.kind = $TK.Mov;
    t2.from = "%edi";
    t2.to = $1.dest;
    info(t2).fixupStack(-4);
    t2.stackdepth = $0.stackdepth;
    $SUBST(t1, t2);
  `));
  mixin(opt("very_specific_resort", `^Push, ^Mov, ^Mov:
    $1.to == "%edi" && $2.from == "%edi" &&
    $1.from != "(%esp)" &&
    $2.to != $0.source && !$0.source.contains($2.to)
    =>
    $T t1 = $1;
    $T t2 = $2;
    info(t1).fixupStack(-4);
    info(t2).fixupStack(-4);
    $SUBST(t1, t2, $0);
  `));
  mixin(opt("mov_into_pop", `^Mov, ^Pop:
    $0.to == "(%esp)" && $1.size == 4
    =>
    $T t1;
    t1.kind = $TK.SFree;
    t1.size = 4;
    $T t2 = $0;
    t2.to = $1.dest;
    info(t2).fixupStack(-4);
    $SUBST(t1, t2);
  `));
  mixin(opt("loopy_push_mov_mov_pop_fold", `^Push, ^Mov, ^Mov, ^Pop:
    $0.size == 4 && $3.size == 4 &&
    $0.source.isIndirect().isUtilityRegister() &&
    $1.from.isIndirect() == "%esp" && $1.to.isUtilityRegister() &&
    $0.source.isIndirect() == $1.to && $0.source.isIndirect() != $2.to && $2.from.isIndirect() == $1.to &&
    $2.to.isUtilityRegister() && $2.to != $1.to &&
    $3.dest == $1.to && $3.dest == $0.source.isIndirect()
    =>
    // mov q(eax) -> eax
    $T t0;
    t0.kind = $TK.Mov;
    t0.from = $0.source;
    t0.to = $3.dest;
    
    // mov r(esp) -> edx
    $T t1 = $1.dup;
    t1.to = $2.to;
    info(t1).fixupStack(-4);
    
    // mov s(edx) -> edx
    $T t2 = $2.dup;
    int delta; $2.from.isIndirect2(delta);
    t2.from = qformat(delta, "(", t1.to, ")");
    info(t2).fixupStack(-4);
    
    $SUBST(t0, t1, t2);
  `));
  mixin(opt("pointless_fxch", `^PureFloat, ^FloatMath:
    $0.opName == "fxch" && $1.opName.isCommutative() && !$1.floatSelf && !$1.op1
    =>
    $SUBST($1);
  `));
  mixin(opt("load_math_direct", `^FloatLoad, ^FloatLoad, ^FloatMath:
    !$2.op1 && !$2.floatSelf
    =>
    $T t = $2;
    t.op1 = $0.source;
    $SUBST($1, t);
  `));
  mixin(opt("load_math_direct_2", `^FloatLoad, ^FloatMath:
    !$1.op1 && !$1.floatSelf && $1.opName.isCommutative()
    =>
    $T t = $1;
    t.op1 = $0.source;
    $SUBST(t);
  `));
  mixin(opt("load_math_direct_3", `^FloatLoad, ^PureFloat, ^FloatMath:
    !$2.op1 && !$2.floatSelf && $1.opName == "fxch"
    =>
    $T t = $2;
    t.op1 = $0.source;
    $SUBST(t);
  `));
}
