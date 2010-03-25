module assemble;

import ast.types;

import tools.base: Format, New, or;
import tools.compat: find, abs;

bool isRelative(string reg) {
  return reg.find("(") != -1;
}

struct Transaction {
  enum Kind {
    Mov, SAlloc, SFree, MathOp
  }
  Kind kind;
  string toAsm() {
    switch (kind) {
      case Kind.Mov:
        if (from.isRelative() && to.isRelative()) {
          assert(usableScratch, "Cannot do relative memmove without scratch register! ");
          return Format("movl ", from, ", ", usableScratch, "\nmovl ", usableScratch, ", ", to);
        } else {
          return Format("movl ", from, ", ", to);
        }
      case Kind.SAlloc: return Format("subl $", size, ", %esp");
      case Kind.SFree: return Format("addl $", size, ", %esp");
      case Kind.MathOp:
        if (opName == "addl" && op1 == "$1") return Format("incl ", op2);
        if (opName == "subl" && op1 == "$1") return Format("decl ", op2);
        return Format(opName, " ", op1, ", ", op2);
    }
  }
  union {
    struct { // Mov
      string from, to;
      string usableScratch;
    }
    struct {
      int size;
    }
    struct {
      string opName;
      string op1, op2;
    }
  }
}

struct Transsection(C) {
  Transcache parent;
  C cond;
  int from, to;
  bool modded;
  Transaction opIndex(int i) { return parent.list[from + i]; }
  size_t length() { return to - from; }
  void replaceWith(Transaction[] withWhat) {
    parent.list = parent.list[0 .. from] ~ withWhat ~ parent.list[to .. $];
    to = from + withWhat.length;
    modded = true;
  }
  void replaceWith(Transaction withWhat) {
    parent.list = parent.list[0 .. from] ~ withWhat ~ parent.list[to .. $];
    to = from + 1;
    modded = true;
  }
  bool advance() {
    auto start = from;
    // don't recheck if not modified
    if (!modded) start = to;
    *this = parent.findMatch(cond, start);
    return from != to;
  }
}

class Transcache {
  Transaction[] list;
  Transsection!(C) findMatch(C)(C cond, int from = 0) {
    for (int base = from; base < list.length; ++base) {
      if (auto len = cond(list[base .. $])) return Transsection!(C)(this, cond, base, base + len, false);
    }
    return Transsection!(C)(this, cond, 0, 0, false);
  }
  void opCatAssign(Transaction t) { list ~= t; }
}

import tools.functional: map;
class AsmFile {
  ubyte[][string] constants;
  string code;
  this() { New(cache); }
  void pushStack(string addr, Type type) {
    assert(type.size == 4);
    salloc(type.size);
    mmove4(addr, "(%esp)");
  }
  Transcache cache;
  // migratory move; contents of source become irrelevant
  void mmove4(string from, string to) {
    Transaction t;
    t.kind = Transaction.Kind.Mov;
    t.from = from; t.to = to;
    cache ~= t;
  }
  void salloc(int sz) { // alloc stack space
    Transaction t;
    t.kind = Transaction.Kind.SAlloc;
    t.size = sz;
    cache ~= t;
  }
  void sfree(int sz) { // alloc stack space
    Transaction t;
    t.kind = Transaction.Kind.SFree;
    t.size = sz;
    cache ~= t;
  }
  void mathOp(string which, string op1, string op2) {
    Transaction t;
    t.kind = Transaction.Kind.MathOp;
    t.opName = which;
    t.op1 = op1; t.op2 = op2;
    cache ~= t;
  }
  // opts
  void collapseAllocFrees() {
    auto match = cache.findMatch((Transaction[] list) {
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
  void collapseAdjacentMoves() {
    auto match = cache.findMatch((Transaction[] list) {
      auto match = Transaction.Kind.Mov;
      if (list.length >= 2 && list[0].kind == match && list[1].kind == match && list[0].to == list[1].from)
        return 2;
      else return cast(int) false;
    });
    if (!match.length) return;
    do {
      // circular.
      if (match[0].from == match[1].to) {
        match.replaceWith(null);
        continue;
      }
      Transaction res;
      res.kind = Transaction.Kind.Mov;
      res.from = match[0].from; res.to = match[1].to;
      if (!match[0].to.isRelative())
        res.usableScratch = match[0].to;
      match.replaceWith(res);
    } while (match.advance());
  }
  // add esp, move, sub esp; or reverse
  void collapsePointlessRegMove() {
    auto match = cache.findMatch((Transaction[] list) {
      auto match = Transaction.Kind.Mov;
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
    auto match = cache.findMatch((Transaction[] list) {
      if (list.length < 3) return 0;
      if ( list[0].kind == Transaction.Kind.Mov && list[0].to == "(%esp)"
        && list[1].kind == Transaction.Kind.Mov && !dependsOnEsp(list[1])
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
  }
  static bool dependsOnEsp(Transaction t) {
    assert(t.kind == Transaction.Kind.Mov);
    return t.from.find("%esp") != -1 || t.to.find("%esp") != -1;
  }
  void sortByEspDependency() {
    auto match = cache.findMatch((Transaction[] list) {
      auto match = Transaction.Kind.Mov;
      if (list.length < 2) return 0;
      if ( list[0].kind == Transaction.Kind.SFree /or/ Transaction.Kind.SAlloc
        && list[1].kind == Transaction.Kind.Mov && !dependsOnEsp(list[1]))
      {
        return 2;
      } else return 0;
    });
    if (match.length) do {
      match.replaceWith([match[1], match[0]]);
    } while (match.advance());
  }
  void flush() {
    collapseAllocFrees();
    collapseAdjacentMoves();
    collapsePointlessRegMove();
    sortByEspDependency();
    collapseAllocFrees(); // rerun
    binOpMathSpeedup();
    foreach (t; cache.list) {
      _put(t.toAsm());
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
