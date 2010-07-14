module ast.base;

public import asmfile, ast.types, parseBase;

static import tools.base;
alias tools.base.Format Format;
alias tools.base.New New;

interface Iterable {
  void iterate(void delegate(ref Iterable) dg);
}

interface Tree : Iterable {
  void emitAsm(AsmFile);
}

import tools.ctfe;
string genIterates(int params) {
  if (params < 0) return null;
  string res = "template defaultIterate(";
  for (int i = 0; i < params; ++i) {
    if (i) res ~= ", ";
    res ~= "alias A"~ctToString(i);
  }
  res ~= ") {
    override void iterate(void delegate(ref Iterable) dg) {";
  for (int i = 0; i < params; ++i) {
    res ~= `
      {
        static if (is(typeof($A[0]))) {
          foreach (i, ref entry; $A) {
            Iterable iter = entry;
            dg(iter);
            if (iter !is entry) {
              auto res = cast(typeof(entry)) iter;
              if (!res) throw new Exception(Format("Cannot substitute ", $A, "[", i, "] with ", res, ": ", typeof(entry).stringof, " expected! "));
              entry = res;
            }
          }
        } else {
          Iterable iter = $A;
          dg(iter);
          if (iter !is $A) {
            auto res = cast(typeof($A)) iter;
            if (!res) throw new Exception(Format("Cannot substitute ", $A, " with ", res, ": ", typeof($A).stringof, " expected! "));
            $A = res;
          }
        }
      }`.ctReplace("$A", "A"~ctToString(i));
  }
  res ~= "
    }
  }
  ";
  return res ~ genIterates(params - 1);
}

mixin(genIterates(9));

// has setup to do on asmfile that are unrelated to pushing value on stack
// example: literals that have to move stuff to the text segment
interface Setupable {
  void setup(AsmFile);
}

interface Named {
  string getIdentifier();
}

interface Statement : Tree { }

class NoOp : Statement {
  override void emitAsm(AsmFile af) { }
  mixin defaultIterate!();
}

interface Expr : Tree {
  IType valueType();
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
interface Cond : Iterable {
  void jumpOn(AsmFile af, bool cond, string dest);
}

class Register(string Reg) : Expr {
  mixin defaultIterate!();
  override IType valueType() { return Single!(SysInt); }
  override void emitAsm(AsmFile af) {
    af.pushStack("%"~Reg, valueType());
  }
}

class Symbol : Expr {
  string name;
  this(string name) { this.name = name; }
  mixin defaultIterate!();
  override IType valueType() { return Single!(SysInt); }
  override void emitAsm(AsmFile af) {
    af.pushStack("$"~name, valueType());
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

void withTLS(T, U, V)(T obj, U value, lazy V vee) {
  auto backup = obj();
  scope(exit) obj.set(backup);
  obj.set(value);
  static if (is(typeof(vee()()))) vee()();
  else static if (is(typeof(vee()))) vee();
  else static assert(false, "Can't call "~V.stringof);
}

/// can be transformed into an obj relative to a base
interface RelTransformable {
  Object transform(Expr base);
}
