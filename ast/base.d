module ast.base;

public import asmfile, ast.types, parseBase;

static import tools.base;
alias tools.base.Format Format;
alias tools.base.New New;

interface Tree {
  void emitAsm(AsmFile);
}

class NoOp : Tree {
  override void emitAsm(AsmFile af) { }
}

interface Statement : Tree { }

interface Expr : Tree {
  Type valueType();
}

interface LValue : Expr {
  void emitLocation(AsmFile);
}

// more than rvalue, less than lvalue
interface MValue : Expr {
  void emitAssignment(AsmFile); // eat value from stack and store
}

/// Emitting this sets up FLAGS.
/// TODO: how does this work on non-x86?
interface Cond {
  void jumpOn(AsmFile af, bool cond, string dest);
}

class Register(string Reg) : Expr {
  override Type valueType() { return new SysInt; }
  override void emitAsm(AsmFile af) {
    af.pushStack("%"~Reg, valueType());
  }
}

string error; // TODO: tls

class ParseException {
  string where, info;
  this(string where, string info) {
    this.where = where; this.info = info;
  }
}

ulong uid;
ulong getuid() { synchronized return uid++; }

// quick and dirty singleton
template _Single(T, U...) {
  T value;
  static this() { value = new T(U); }
}

template Single(T, U...) {
  static assert(is(T: Object));
  alias _Single!(T, U).value Single;
}
