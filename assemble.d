module assemble;

import ast.base;

import tools.base: New, or, and, slice, between, fail;
import tools.compat: find, abs, replace, atoi;
import tools.log;

bool isRelative(string reg) {
  if (!reg.length) { asm { int 3; } }
  return reg.find("(") != -1 || reg.find("@NTPOFF") != -1 || ("%$".find(reg[0]) == -1);
}

bool isMemRef(string mem) {
  if (isRelative(mem)) return true;
  return !mem.startsWith("%") && !mem.startsWith("$");
}

bool isRegister(string s) {
  return s.length > 2 && s[0] == '%' && s[1] != '(';
}

bool contains(string s, string t) {
  if (!t) return false;
  return s.find(t) != -1;
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
  if (!isLiteral(s)) asm { int 3; }
  assert(isLiteral(s), "not a literal: "~s);
  return s[1 .. $].my_atoi();
}

// if false, is either a literal or a register (not esp)
bool mayNeedStack(string str) {
  if (str.find("%esp") != -1) return true;
  return isRelative(str);
}

string isIndirectSimple(string s) {
  if (s.length >= 2 && s[0] == '(' && s[$-1] == ')') {
    return s[1..$-1];
  }
  else return null;
}
string isIndirectComplex(string s, ref int delta, bool allowLiterals) {
  if (s.between(")", "").length) return null;
  auto betw = s.between("(", ")");
  if (betw && (betw.isRegister() || allowLiterals)) {
    delta = s.between("", "(").my_atoi();
    return betw;
  }
  return null;
}
string isIndirect2(string s, ref int delta, bool allowLiterals = false) {
  delta = 0;
  if (auto res = isIndirectSimple(s)) return res;
  if (auto res = isIndirectComplex(s, delta, allowLiterals)) return res;
  return null;
}
string isIndirect(string s, int offs = -1) {
  int bogus;
  if (offs == -1) return isIndirect2(s, bogus);
  else {
    auto res = isIndirect2(s, bogus);
    if (bogus == offs) return res;
    else return null;
  }
}

string fixupLiterals(string s) {
  int offs;
  auto indir = s.isIndirect2(offs, true);
  if (auto rest = indir.startsWith("$")) {
    if (offs != 0) return qformat(rest, "+", offs);
    else return rest;
  }
  return s;
}

interface ExtToken {
  string toAsm();
}

import parseBase; // int parsing
struct Transaction {
  enum Kind {
    Mov, Mov2, Mov1, MovD, SAlloc, SFree, MathOp, Push, Pop, Compare, Call, Swap,
    FloatLoad, DoubleLoad, RealLoad, RegLoad,
    FloatCompare,
    FloatPop, DoublePop, FPIntPop,
    FloatStore, DoubleStore,
    FloatMath, FPSwap,
    FloatLongLoad, FloatIntLoad, /* fildq/l */
    SSEOp,
    ExtendDivide, /* cdq, [i]divl */
    Text,
    Jump, Label, Extended, Nevermind, LoadAddress
  }
  const string[] KindDecode = ["Mov4", "Mov2", "Mov1", "MovD", "SAlloc", "SFree", "MathOp", "Push", "Pop", "Compare", "Call", "Swap",
    "FloatLoad", "DoubleLoad", "RealLoad", "RegLoad",
    "FloatCompare",
    "FloatPop" , "DoublePop", "FPIntPop",
    "FloatStore", "DoubleStore",
    "FloatMath", "FPSwap",
    "FloatLongLoad", "FloatIntLoad",
    "SSEOp",
    "ExtendDivide",
    "Text",
    "Jump", "Label", "Extended", "Nevermind", "LoadAddress"];
  Kind kind;
  string toString() {
    string extra() {
      if (!hasStackdepth) return "@?";
      else return qformat("@", stackdepth);
    }
    with (Kind) switch (kind) {
      case Mov:         return Format("[movl ", from, " -> ", to, stackinfo, "]");
      case Mov2:        return Format("[movw ", from, " -> ", to, stackinfo, "]");
      case Mov1:        return Format("[movb ", from, " -> ", to, stackinfo, "]");
      case MovD:        return Format("[movd ", from, " -> ", to, stackinfo, "]");
      case SAlloc:      return Format("[salloc ", size, "]");
      case SFree:       return Format("[sfree ", size, "]");
      case MathOp:      return Format("[math:", opName, " ", op1, ", ", op2, "]");
      case Push:        return Format("[push ", source, ": ", size, extra(), "]");
      case Pop:         return Format("[pop ", dest, ": ", size, extra(), "]");
      case Call:        return Format("[call ", dest, "]");
      case Swap:        return Format("[swap ", source, ", ", dest, "]");
      case Compare:
        if (test)       return Format("[cmp/test ", op1, ", ", op2, "]");
        else            return Format("[cmp ", op1, ", ", op2, "]");
      case FloatLoad:   return Format("[float load ", source, stackinfo, "]");
      case DoubleLoad:  return Format("[double load ", source, stackinfo, "]");
      case RealLoad:    return Format("[real load ", source, stackinfo, "]");
      case RegLoad:     return Format("[x87 reg load ", source, stackinfo, "]");
      case FloatCompare:return Format("[x87 float compare st0, ", source, stackinfo, "]");
      case FloatPop:    return Format("[float pop ", dest, "]");
      case DoublePop:   return Format("[double pop ", dest, "]");
      case FPIntPop:    return Format("[fp int pop ", dest, "]");
      case FloatStore:  return Format("[float store ", dest, "]");
      case DoubleStore: return Format("[double store ", dest, "]");
      case FloatMath:   return Format("[float math ", opName, " ", floatSelf, "]");
      case FPSwap:      return Format("[x87 swap]");
     case FloatLongLoad:return Format("[float long load ", source, "]");
      case FloatIntLoad:return Format("[float int load ", source, "]");
      case SSEOp:       return Format("[SSE ", opName, " ", op1, ", ", op2, stackinfo, "]");
      case ExtendDivide:return Format("[cdq/idivl ", source, ", ", signed?"signed":"unsigned", "]");
      case Jump:        return Format("[jmp ", dest, keepRegisters?" [keepregs]":"", mode?(" "~mode):"", "]");
      case Label:       return Format("[label ", names, keepRegisters?" [keepregs]":"", "]");
      case Extended:    return Format("[extended ", obj, "]");
      case Nevermind:   return Format("[nvm ", dest, "]");
      case LoadAddress: return Format("[lea ", from, " -> ", to, stackinfo, "]");
      case Text:        return Format("[text ", text, "]");
    }
  }
  int opEquals(ref Transaction t2) {
    if (kind != t2.kind) return false;
    with (Kind) switch (kind) {
      case Mov, Mov2, Mov1, MovD:  return from == t2.from && to == t2.to;
      case SAlloc, SFree: return size == t2.size;
      case MathOp: return opName == t2.opName && op1 == t2.op1 && op2 == t2.op2;
      case Push: return source == t2.source && size == t2.size;
      case Pop: return dest == t2.dest && size == t2.size;
      case FloatStore, DoubleStore, FloatPop, DoublePop, FPIntPop: return dest == t2.dest;
      case Call, Jump: return dest == t2.dest;
      case Swap: return source == t2.source && dest == t2.dest && size == t2.size;
      case Compare: return op1 == t2.op1 && op2 == t2.op2;
      case FloatLoad, DoubleLoad, RealLoad, RegLoad: return source == t2.source;
      case FloatCompare: return source == t2.source && useIVariant == t2.useIVariant;
      case FloatMath: return opName == t2.opName && floatSelf == t2.floatSelf;
      case FPSwap: return true;
      case FloatLongLoad, FloatIntLoad: return source == t2.source;
      case SSEOp: return opName == t2.opName && op1 == t2.op1 && op2 == t2.op2;
      case ExtendDivide: return source == t2.source && signed == t2.signed;
      case Label: return names == t2.names;
      case Extended: return obj == t2.obj;
      case Nevermind: return dest == t2.dest;
      case LoadAddress: return from == t2.from && to == t2.to;
      case Text: return text == t2.text;
    }
    assert(false);
  }
  static string asmformat(string s) {
    if (auto betw = s.between("(", ")")) {
      auto offs = s.between("", "(").my_atoi();
      if (betw.startsWith("$")) {
        return qformat(betw[1 .. $], "+", offs);
      }
      if (betw.startsWith("%esi+$")) {
        auto name = betw.between("+$", "");
        return qformat("(", name, " + ", offs, ")(%esi)");
      }
    }
    return s;
  }
  string toAsm() {
    with (Kind) switch (kind) {
      case MovD:
        return qformat("movd ", from.asmformat(), ", ", to.asmformat());
      case Mov:
        if (from.isRelative() && to.isRelative()) {
          if (!usableScratch) {
            logln("Cannot do relative memmove without scratch register: ", from, " -> ", to);
            fail();
          }
          return qformat("movl ", from.asmformat(), ", ", usableScratch, "\nmovl ", usableScratch, ", ", to.asmformat());
        } else {
          return qformat("movl ", from.asmformat(), ", ", to.asmformat(), " #mov4.2");
        }
      case Mov2:
        if (from.isRelative() && to.isRelative()) {
          assert(usableScratch, Format("Cannot do relative memmove without scratch register: ", from, " -> ", to));
          return qformat("movw ", from.asmformat(), ", ", usableScratch, "\nmovw ", usableScratch, ", ", to.asmformat());
        } else {
          return qformat("movw ", from.asmformat(), ", ", to.asmformat());
        }
      case Mov1:
        if (from.isRelative() && to.isRelative()) {
          assert(usableScratch, Format("Cannot do relative memmove without scratch register: ", from, " -> ", to));
          return qformat("movb ", from.asmformat(), ", ", usableScratch, "\nmovw ", usableScratch, ", ", to.asmformat());
        } else {
          return qformat("movb ", from.asmformat(), ", ", to.asmformat());
        }
      case SAlloc:
          if (!size) return null;
          return qformat("subl $", size, ", %esp # salloc");
      case SFree:
          if (!size) return null;
          return qformat("addl $", size, ", %esp # sfree");
      case MathOp:
        if (opName == "addl" && op1 == "$1") return qformat("incl ", op2);
        if (opName == "subl" && op1 == "$1") return qformat("decl ", op2);
        return qformat(opName, " ", op1, ", ", op2);
      case Push, Pop:
        string res;
        // res = toString();
        // res = "# is " ~ res;
        void addLine(string s) { if (res) res ~= "\n"; res ~= s; }
        auto mnemo = (kind == Push) ? "push" : "pop";
        // %eax
        string matchRegister(string s) {
          string reg;
          if (s.accept_mt("%") && s.gotIdentifier(reg)) {
            if (s.length && s[0] == ':') {
              reg ~= s;
              s = null;
            }
            if (!s.length) return reg;
          }
          return null;
        }
        // $5 or $constant_string
        bool gotLiteral(string s, ref int num, ref string ident) {
          return s.accept_mt("$") && (s.gotInt(num) || (s.find("(") == -1) && (ident = s, s = null, true)) && !s.length;
        }
        // $5
        bool gotIntLiteral(string s, ref int num) {
          return s.accept_mt("$") && s.gotInt(num);
        }
        // 8(%eax) or 8($literal)
        string gotMemoryOffset(string s, ref int offs) {
//           string prefix, reference;
          auto betw = s.between("(", ")");
          if (!betw) return null;
          auto s2 = s;
          if (!s2.gotInt(offs)) offs = 0;
          return betw;
        }
        // push/pop as far as possible at that size sz, using instruction postfix pf.
        auto op = (kind == Push) ? source : dest;
        int first_offs = -1;
        int stack_changed;
        void doOp(int sz, string pf) {
          while (size >= sz) {
            bool m_offs_push; int offs;
            if (kind == Push) {
              /*if (op.between("(", ")").startsWith("%esi+")) {
                auto varname = op.between("%esi+", ")");
                offs = op.between("", "(").my_atoi();
                if (first_offs != -1) offs = first_offs;
                else first_offs = offs;
                op = qformat(first_offs + size - sz, "(%esi+", varname, ")");
                m_offs_push = true;
                
              }*/
              if (auto mem = op.gotMemoryOffset(offs)) {
                if (first_offs != -1) offs = first_offs;
                else first_offs = offs;
                // logln("rewrite op ", op, " to ", qformat(first_offs + size - sz, "(%", reg, ")"), ": ", first_offs, " + ", size, " - ", sz); 
                op = qformat(first_offs + size - sz + ((mem.contains("%esp"))?stack_changed:0), "(", mem, ")");
                m_offs_push = true;
              }
              if (op.startsWith("+")) {
                logln(op, " (", *this, ")");
                asm { int 3; }
              }
            }
            if (sz == 1) { // not supported in hardware
              if (kind == Push) {
                addLine("decl %esp");
                addLine("pushw %bx");
                addLine("movb "~op~", %bl");
                addLine("movb %bl, 2(%esp)");
                addLine("popw %bx");
              } else {
                addLine("pushw %bx");
                string opsh = op;
                // hackaround
                if (opsh.isIndirect2(offs).contains("%esp"))
                  opsh = qformat(offs - 1, "(", opsh.isIndirect(), ")");
                addLine("movb 2(%esp), %bl");
                addLine("movb %bl, "~opsh);
                addLine("popw %bx");
                addLine("incl %esp");
              }
            // x86 pop foo(%esp) operand is evaluated
            // after increment, says intel manual
            } else {
              if (kind == Pop && op.isIndirect2(offs).contains("%esp")) {
                op = qformat(offs - sz, "(", op.isIndirect(), ")");
              }
              auto temp = op; int toffs;
              temp = asmformat(temp);
              if (temp.startsWith("+")) {
                logln(temp, " (", *this, ")");
                asm { int 3; }
              }
              addLine(qformat(mnemo, pf, " ", temp, " #", size));
              stack_changed += sz;
            }
            auto s2 = op;
            int num; string ident, reg;
            if (null !is (reg = op.matchRegister())) {
              auto regsize = (reg[0] == 'e')?4:(reg[0] == 'r')?8:(reg[$-1]== 'l' /or/ 'h')?1:2;
              if (size != regsize)
                throw new Exception(Format("Can't pop/push ", size, " of ", reg, ": size mismatch! "));
            }
            else if (kind == Push && op.gotLiteral(num, ident)) {
              // just duplicate the number
              // if (size != sz) throw new Exception(Format("Can't push ", size, " of ", ident?ident:Format(num), ": size mismatch! "));
            }
            else if (kind == Pop && null !is (reg = op.gotMemoryOffset(offs))) {
              op = qformat(offs + sz, "(", reg, ")");
            }
            else if (kind == Push && null !is (reg = op.gotMemoryOffset(offs))) {
              op = qformat(offs + sz, "(", reg, ")");
            }
            else if (!m_offs_push && (op.find("%") != -1 || op.find("(") != -1))
              throw new Exception("Unknown address format: '"~op~"'");
            size -= sz;
          }
        }
        // doOp(8, "r");
        doOp(4, "l");
        doOp(2, "w");
        doOp(1, "b");
        return res;
      case Compare:
        if (test) return qformat("testl ", op1, ", ", op2);
        else return qformat("cmpl ", op1, ", ", op2);
      case Call:
        if (dest.find("%") != -1) return qformat("call *", dest);
        if (dest[0] == '$') return qformat("call ", dest[1 .. $]);
        assert(false, "::"~dest);
      case Swap:
        if (size == 4) return qformat("xchgl ", source.fixupLiterals(), ", ", dest.fixupLiterals());
        if (size == 2) return qformat("xchgw ", source.fixupLiterals(), ", ", dest.fixupLiterals());
        if (size == 1) return qformat("xchgb ", source.fixupLiterals(), ", ", dest.fixupLiterals());
        assert(false, Format(this, "#", size));
      case FloatLoad: return qformat("flds ", source.fixupLiterals());
      case DoubleLoad: return qformat("fldl ", source.fixupLiterals());
      case RealLoad: return qformat("fldt ", source.fixupLiterals());
      case RegLoad: return qformat("fld ", source);
      case FloatCompare:
        if (useIVariant) {
          if (source != "%st(1)")
            throw new Exception("fcomi require ST1 arg! ");
          return qformat("fcomip\nfstp %st"); // fcomipp
        }
        if (source == "%st(1)") {
          return qformat("fcompp");
        }
        return qformat("fcomps ", source);
      case FloatPop: return qformat("fstps ", dest);
      case DoublePop: return qformat("fstpl ", dest);
      case FPIntPop: return qformat("fistpl ", dest);
      case FloatStore: return qformat("fsts ", dest);
      case DoubleStore: return qformat("fstl ", dest);
      case FloatMath:
        if (opName == "fsqrt") return opName;
        if (floatSelf) return qformat(opName, " %st, %st");
        else return qformat(opName, "p %st, %st(1)");
      case FPSwap: return qformat("fxch");
      case FloatLongLoad: return qformat("fildq ", source);
      case FloatIntLoad: return qformat("fildl ", source);
      case SSEOp: return qformat(opName, " ", op1, ", ", op2);
      case ExtendDivide:
        if (signed) return qformat("cdq\nidivl ", source);
        else return qformat("xorl %edx, %edx\ndivl ", source); // no sign extension if unsigned, duh
      case Jump: if (mode) return qformat(mode, " ", dest); return qformat("jmp ", dest);
      case Label:
        assert(names.length);
        string res;
        if (!isWindoze())
          res ~= ".p2align 4, 0x90\n";
        foreach (name; names) res ~= name ~ ":\n";
        return res[0 .. $-1];
      case Extended: return obj.toAsm();
      case Nevermind: return qformat("#forget ", dest, ". ");
      case LoadAddress: return qformat("leal ", from.asmformat(), ", ", to);
      case Text: return text;
    }
  }
  struct {
    union {
      struct { // Mov
        string from, to;
        string usableScratch;
      }
      struct {
        int size;
        string source, dest;
      }
      struct {
        string opName;
        string op1, op2, op3;
        bool test;
      }
      struct { // label
        string[] names;
      }
      bool hasLabel(string s) { foreach (name; names) if (name == s) return true; return false; }
      ExtToken obj;
    }
    bool keepRegisters;
    bool floatSelf;
    union {
      bool signed;
      bool useIVariant;
    }
    int stackdepth = -1;
    union {
      string mode; // for jumps
      string text; // for literals
    }
  }
  bool hasStackdepth() { return stackdepth != -1; }
  string stackinfo() { return stackdepth == -1 ? "" : qformat("@", stackdepth); }
  Transaction dup() {
    Transaction res = *this;
    res.stackdepth = -1;
    return res;
  }
}

bool debugOpts;

import tools.compat: max;

struct Transsection(C) {
  Transcache parent;
  string opName;
  C cond;
  int from, to;
  bool modded;
  Transaction opIndex(int i) { return parent.list[from + i]; }
  Transaction[] opSlice() { return parent.list[from .. to]; }
  size_t length() { return to - from; }
  void replaceWith(T...)(T t) {
    if (debugOpts)
      logln(opName, ": ", parent.list[from .. to], " -> ", t);
    int tlength;
    foreach (elem; t)
      static if (is(typeof(elem.length))) tlength += elem.length;
      else tlength ++;
    
    if (tlength == length) {
      int offs = from;
      foreach (elem; t) {
        static if (is(typeof(elem.length))) {
          for (int i = 0; i < elem.length; ++i)
            parent.list[i+offs] = elem[i];
          offs += elem.length;
        } else { parent.list[offs++] = elem; }
      }
    } else {
      with (parent) {
        auto f1 = to, t1 = size, f2 = from + tlength, t2 = f2 + (t1 - f1);
        resize(max(size, t2));
        if (f2 < f1) { // backward copy; copy, then stretch
          int offs = from;
          foreach (elem; t)
            static if (is(typeof(elem.length))) {
              for (int i = offs; i < offs + elem.length; ++i)
                list[i] = elem[i - offs];
              offs += elem.length;
            } else {
              list[offs++] = elem;
            }
          for (int i = f1; i < t1; ++i)
            list[f2 - f1 + i] = list[i];
        } else { // forward copy; stretch, then copy
          for (int i = t1 - 1; i >= f1; --i)
            list[f2 - f1 + i] = list[i];
          int offs = f2;
          foreach_reverse (elem; t)
            static if (is(typeof(elem.length))) {
              for (int i = offs - 1; i >= cast(int) (offs - elem.length); --i) {
                list[i] = elem[i - offs + $];
              }
              offs -= elem.length;
            } else {
              list[--offs] = elem;
            }
        }
        size = t2;
      }
      // parent.list = parent.list[0 .. from] ~ withWhat ~ parent.list[to .. $];
    }
    to = from + tlength;
    modded = true;
  }
  bool reset() {
    *this = parent.findMatch(opName, cond);
    return !!length;
  }
  bool advance() {
    auto start = from;
    // don't recheck if not modified
    if (!modded) start = start + 1;
    *this = parent.findMatch(opName, cond, start);
    return !!length;
  }
}

class Transcache {
  Transaction[] _list;
  int size;
  final void resize(int i) {
    if (!_list.length) _list = new Transaction[1024];
    while (_list.length < i) _list.length = _list.length * 2;
    size = i;
  }
  final Transaction[] list() {
    debug if (size > _list.length) {
      logln("WTF?! ", size, " into ", _list.length);
      asm { int 3; }
    }
    return _list[0 .. size];
  }
  Transsection!(C) findMatch(C)(string opName, C cond, int from = 0) {
    for (int base = from; base < list.length; ++base) {
      if (auto len = cond(list[base .. $])) return Transsection!(C)(this, opName, cond, base, base + len, false);
    }
    return Transsection!(C)(this, opName, cond, 0, 0, false);
  }
  final void clear() { size = 0; }
  final void opCatAssign(Transaction t) {
    if (!_list.length) _list = new Transaction[1024];
    if (size == _list.length) _list.length = _list.length * 2;
    _list[size++] = t;
  }
  final void opCatAssign(Transaction[] newlist) {
    if (!_list.length) { _list = newlist.dup; size = newlist.length; return; }
    while (size + newlist.length > _list.length) _list.length = _list.length * 2;
    _list[size .. size + newlist.length] = newlist;
    size += newlist.length;
  } 
}
