module ast.base;

public import asmfile, ast.types, parseBase;

static import tools.base;
alias tools.base.Format Format;
alias tools.base.New New;

interface Tree {
  void emitAsm(AsmFile);
}

// has setup to do on asmfile that are unrelated to pushing value on stack
// example: literals that have to move stuff to the text segment
interface Setupable {
  void setup(AsmFile);
}

interface Statement : Tree { }

class NoOp : Statement {
  override void emitAsm(AsmFile af) { }
}

interface Expr : Tree {
  Type valueType();
}

// has a pointer, but please don't modify it - ie. string literals
interface CValue : Expr {
  void emitLocation(AsmFile);
}

// free to modify
interface LValue : CValue {
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
  override Type valueType() { return Single!(SysInt); }
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

void withTLS(T, U, V)(T obj, U value, lazy V vee) {
  auto backup = obj();
  scope(exit) obj.set(backup);
  obj.set(value);
  static if (is(typeof(vee()()))) vee()();
  else static if (is(typeof(vee()))) vee();
  else static assert(false, "Can't call "~V.stringof);
}
