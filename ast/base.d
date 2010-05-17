module ast.base;

public import asmfile, ast.types, parseBase;

static import tools.base;
alias tools.base.Format Format;
alias tools.base.New New;

interface Tree {
  void emitAsm(AsmFile);
}

interface Statement : Tree { }

interface Expr : Statement {
  Type valueType();
}

interface LValue : Expr {
  void emitLocation(AsmFile);
}

/// Emitting this sets up FLAGS.
/// TODO: how does this work on non-x86?
interface Cond : Statement {
  void jumpFalse(AsmFile af, string dest);
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
