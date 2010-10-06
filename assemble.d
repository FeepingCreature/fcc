module assemble;

import ast.types;

import tools.base: Format, New, or, and, slice, between;
import tools.compat: find, abs, replace, atoi;
import tools.log;

bool isRelative(string reg) {
  return reg.find("(") != -1 || reg.find("@NTPOFF") != -1;
}

bool isMemRef(string mem) {
  if (isRelative(mem)) return true;
  return !mem.startsWith("%") && !mem.startsWith("$");
}

// if false, is either a literal or a register (not esp)
bool mayNeedStack(string str) {
  if (str.find("%esp") != -1) return true;
  return isRelative(str);
}

interface ExtToken {
  string toAsm();
}

import parseBase; // int parsing
struct Transaction {
  enum Kind {
    Mov, Mov2, Mov1, SAlloc, SFree, MathOp, Push, Pop, Compare, Call,
    FloatLoad, FloatStore, FloatPop, FloatMath, FloatSwap,
    Jump, Label, Extended, Nevermind
  }
  const string[] KindDecode = ["Mov4", "Mov2", "Mov1", "SAlloc", "SFree", "MathOp", "Push", "Pop", "Compare", "Call",
    "FloatLoad", "FloatStore", "FloatPop", "FloatMath", "FloatSwap",
    "Jump", "Label", "Extended", "Nevermind"];
  Kind kind;
  string toString() {
    switch (kind) {
      case Kind.Mov:     return Format("[movl ", from, " -> ", to, "]");
      case Kind.Mov2:    return Format("[movw ", from, " -> ", to, "]");
      case Kind.Mov1:    return Format("[movb ", from, " -> ", to, "]");
      case Kind.SAlloc:  return Format("[salloc ", size, "]");
      case Kind.SFree:   return Format("[sfree ", size, "]");
      case Kind.MathOp:  return Format("[math:", opName, " ", op1, ", ", op2, "]");
      case Kind.Push:    return Format("[push ", source, ": ", type.size, "]");
      case Kind.Pop:     return Format("[pop ", dest, ": ", type.size, "]");
      case Kind.Call:    return Format("[call ", dest, "]");
      case Kind.Compare:
        if (test) return Format("[cmp/test ", op1, ", ", op2, "]");
        else return Format("[cmp ", op1, ", ", op2, "]");
      case Kind.FloatLoad: return Format("[float load ", source, stackinfo, "]");
      case Kind.FloatStore: return Format("[float store ", dest, "]");
      case Kind.FloatPop:  return Format("[float pop ", dest, "]");
      case Kind.FloatMath: return Format("[float math ", opName, "]");
      case Kind.FloatSwap: return Format("[float swap]");
      case Kind.Jump:      return Format("[jmp ", dest, "]");
      case Kind.Label:     return Format("[label ", names, "]");
      case Kind.Extended:  return Format("[extended ", obj, "]");
      case Kind.Nevermind: return Format("[nvm ", dest, "]");
    }
  }
  string toAsm() {
    switch (kind) {
      case Kind.Mov:
        if (from.isRelative() && to.isRelative()) {
          assert(usableScratch, Format("Cannot do relative memmove without scratch register: ", from, " -> ", to));
          return Format("movl ", from, ", ", usableScratch, "\nmovl ", usableScratch, ", ", to);
        } else {
          return Format("movl ", from, ", ", to);
        }
      case Kind.Mov2:
        if (from.isRelative() && to.isRelative()) {
          assert(usableScratch, Format("Cannot do relative memmove without scratch register: ", from, " -> ", to));
          return Format("movw ", from, ", ", usableScratch, "\nmovw ", usableScratch, ", ", to);
        } else {
          return Format("movw ", from, ", ", to);
        }
      case Kind.Mov1:
        if (from.isRelative() && to.isRelative()) {
          assert(usableScratch, Format("Cannot do relative memmove without scratch register: ", from, " -> ", to));
          return Format("movb ", from, ", ", usableScratch, "\nmovw ", usableScratch, ", ", to);
        } else {
          return Format("movb ", from, ", ", to);
        }
      case Kind.SAlloc:
          if (!size) return null;
          return Format("subl $", size, ", %esp");
      case Kind.SFree:
          if (!size) return null;
          return Format("addl $", size, ", %esp");
      case Kind.MathOp:
        if (opName == "addl" && op1 == "$1") return Format("incl ", op2);
        if (opName == "subl" && op1 == "$1") return Format("decl ", op2);
        return Format(opName, " ", op1, ", ", op2);
      case Kind.Push, Kind.Pop:
        auto size = type.size;
        string res;
        void addLine(string s) { if (res) res ~= "\n"; res ~= s; }
        auto mnemo = (kind == Kind.Push) ? "push" : "pop";
        // %eax
        string matchRegister(string s) {
          string reg;
          if (s.accept("%") && s.gotIdentifier(reg)) {
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
          return s.accept("$") && (s.gotInt(num) || (s.find("(") == -1) && (ident = s, s = null, true)) && !s.length;
        }
        // 8(%eax)
        string gotMemoryOffset(string s, ref int offs) {
          string reg;
          if ((s.gotInt(offs) || (offs = 0, true)) && s.accept("(%") && s.gotIdentifier(reg) && s.accept(")")) return reg;
          else return null;
        }
        // push/pop as far as possible at that size sz, using instruction postfix pf.
        auto op = (kind == Kind.Push) ? source : dest;
        int first_offs = -1;
        void doOp(int sz, string pf) {
          while (size >= sz) {
            bool m_offs_push; int offs;
            if (kind == Kind.Push) {
              if (op.startsWith("%gs:") && op.find("@") != -1) {
                offs = op.between("+", "").atoi();
                string varname = op.between(":", "@");;
                if (first_offs != -1) offs = first_offs;
                else first_offs = offs;
                // logln("tls rewrite op ", op, " to ", "%gs:", varname, "@NTPOFF+", first_offs + size - sz, ": ", first_offs, " + ", size, " - ", sz); 
                op = Format("%gs:", varname, "@NTPOFF+", first_offs + size - sz);
                m_offs_push = true;
                
              }
              if (auto reg = op.gotMemoryOffset(offs)) {
                if (first_offs != -1) offs = first_offs;
                else first_offs = offs;
                // logln("rewrite op ", op, " to ", Format(first_offs + size - sz, "(%", reg, ")"), ": ", first_offs, " + ", size, " - ", sz); 
                op = Format(first_offs + size - sz, "(%", reg, ")");
                m_offs_push = true;
              }
            }
            if (sz == 1) { // not supported in hardware
              // hackaround
              addLine("pushw %bx");
              if (kind == Kind.Push) {
                addLine("movb "~op~", %bl");
                addLine("decl %esp");
                addLine("movb %bl, (%esp)");
              } else {
                addLine("movb (%esp), %bl");
                addLine("incl %esp");
                addLine("movb %bl, "~op);
              }
              addLine("popw %bx");
            } else {
              addLine(Format(mnemo, pf, " ", op));
            }
            auto s2 = op;
            int num; string ident, reg;
            if (null !is (reg = op.matchRegister())) {
              if (reg.startsWith("gs:") && reg.find("@") != -1) {
                auto temp = reg, reg_offs = temp.slice("+").atoi(), varname = reg.between(":", "@");
                assert(reg.between("@", "").startsWith("NTPOFF"));
                op = Format("%gs:", varname, "@NTPOFF+", reg_offs + sz);
              } else {
                auto regsize = (reg[0] == 'e')?4:(reg[0] == 'r')?8:(reg[$-1]== 'l' /or/ 'h')?1:2;
                if (reg.startsWith("gs:")) regsize = nativePtrSize;
                if (size != regsize)
                  throw new Exception(Format("Can't pop/push ", type, " of ", reg, ": size mismatch! "));
              }
            }
            else if (kind == Kind.Push && op.gotLiteral(num, ident)) {
              // just duplicate the number
              // if (size != sz) throw new Exception(Format("Can't push ", type, " of ", ident?ident:Format(num), ": size mismatch! "));
            }
            else if (kind == Kind.Pop && null !is (reg = op.gotMemoryOffset(offs))) {
              op = Format(offs + sz, "(%", reg, ")");
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
      case Kind.Compare:
        if (test) return Format("testl ", op1, ", ", op2);
        else return Format("cmpl ", op1, ", ", op2);
      case Kind.Call:
        if (dest.find("%") != -1) return Format("call *", dest);
        if (dest[0] == '$') return Format("call ", dest[1 .. $]);
        assert(false, "::"~dest);
      case Kind.FloatLoad:
        return Format("flds ", source);
      case Kind.FloatPop:
        return Format("fstps ", dest);
      case Kind.FloatStore:
        return Format("fsts ", dest);
      case Kind.FloatMath:
        return Format(opName~"p %st, %st(1)");
      case Kind.FloatSwap:
        return Format("fxch");
      case Kind.Jump:
        return Format("jmp ", dest);
      case Kind.Label:
        assert(names.length);
        string res;
        foreach (name; names) res ~= name ~ ":\n";
        return res[0 .. $-1];
      case Kind.Extended:
        return obj.toAsm();
      case Kind.Nevermind:
        return null;
    }
  }
  struct {
    union {
      struct { // Mov
        string from, to;
        string usableScratch;
      }
      int size;
      struct {
        string source, dest;
        IType type;
      }
      struct {
        string opName;
        string op1, op2, op3;
        bool test;
      }
      string[] names; // label
      bool hasLabel(string s) { foreach (name; names) if (name == s) return true; return false; }
      ExtToken obj;
    }
    int stackdepth = -1;
  }
  bool hasStackdepth() { return stackdepth != -1; }
  string stackinfo() { return stackdepth == -1 ? "" : Format("@", stackdepth); }
  Transaction dup() {
    Transaction res = *this;
    res.stackdepth = -1;
    return res;
  }
}

bool debugOpts;

struct Transsection(C) {
  Transcache parent;
  string opName;
  C cond;
  int from, to;
  bool modded;
  Transaction opIndex(int i) { return parent.list[from + i]; }
  Transaction[] opSlice() { return parent.list[from .. to]; }
  size_t length() { return to - from; }
  void replaceWith(Transaction[] withWhat) {
    if (debugOpts) logln(opName, ": ", parent.list[from .. to], " -> ", withWhat);
    if (withWhat.length == length) {
      parent.list[from .. to] = withWhat;
    } else {
      parent.list = parent.list[0 .. from] ~ withWhat ~ parent.list[to .. $];
    }
    to = from + withWhat.length;
    modded = true;
  }
  void replaceWith(Transaction withWhat) {
    if (debugOpts) logln(opName, ": ", parent.list[from .. to], " -> ", withWhat);
    if (length == 1) {
      parent.list[from] = withWhat;
    } else {
      parent.list = parent.list[0 .. from] ~ withWhat ~ parent.list[to .. $];
    }
    to = from + 1;
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
  Transaction[] list;
  Transsection!(C) findMatch(C)(string opName, C cond, int from = 0) {
    for (int base = from; base < list.length; ++base) {
      if (auto len = cond(list[base .. $])) return Transsection!(C)(this, opName, cond, base, base + len, false);
    }
    return Transsection!(C)(this, opName, cond, 0, 0, false);
  }
  void opCatAssign(Transaction t) {
    list ~= t;
  }
}
