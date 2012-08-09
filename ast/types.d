module ast.types;

import tools.base: Stuple, take;

import alloc, casts, dwarf2, asmfile, quickformat;

interface IType {
  int size();
  string mangle();
  ubyte[] initval();
  int opEquals(IType);
  // return the type we are a proxy for, or null
  // (proxy == type alias)
  IType proxyType();
  bool isPointerLess(); // concerns the VALUE ITSELF - ie. an array is always pointerful
  bool isComplete(); // is this type completely defined or does it depend on future stuff?
}

import tools.log;
// Strips out type-alias and the like
IType resolvecache;
IType resolveType(IType t) {
  if (t is resolvecache) return t; // shortcut for repeated call
  while (t) {
    if (auto tp = t.proxyType()) {
      t = tp;
      continue;
    }
    break;
  }
  resolvecache = t;
  return t;
}

template TypeDefaults(bool INITVAL = true, bool OPEQUALS = true) {
  static if (INITVAL) ubyte[] initval() { return new ubyte[size()]; }
  static if (OPEQUALS) {
    int opEquals(IType ty) {
      // specialize where needed
      ty = resolveType(ty);
      auto obj = cast(Object) (cast(void*) (ty) - (***cast(Interface***) ty).offset);
      return
        (this.classinfo is obj.classinfo)
        &&
        (size == (cast(typeof(this)) cast(void*) obj).size);
    }
  }
  IType proxyType() { return null; }
}

string registerType(Dwarf2Controller dwarf2, Dwarf2Encodable d2e) {
  return dwarf2.addToRoot(
    qformat(d2e),
    d2e.encode(dwarf2)
  );
}

class Type : IType {
  mixin TypeDefaults!();
  abstract int size();
  abstract string mangle();
  bool isPointerLess() { return false; } // default
  bool isComplete() { return true; } // also default
  string toString() { return mangle(); }
}

class Void_ : Type, Dwarf2Encodable {
  override {
    int size() { return 1; }
    string mangle() { return "void"; }
    ubyte[] initval() { return null; }
    string toString() { return "void"; }
    bool canEncode() { return true; }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("base type"[]));
      with (sect) {
        data ~= ".int\t0\t/* byte size */";
        data ~= qformat(".byte\t"[], hex(DW.ATE_void), "\t/* void */"[]);
        data ~= dwarf2.strings.addString("void"[]);
      }
      return sect;
    }
  }
}

final class Void : Void_ { }

final class Variadic : Type {
  override int size() { assert(false); }
  /// BAH
  // TODO: redesign parameter match system to account for automatic conversions in variadics.
  override string mangle() { return "variadic"; }
  override ubyte[] initval() { assert(false, "Cannot declare variadic variable. "[]); } // wtf variadic variable?
}

class Char_ : Type, Dwarf2Encodable {
  override {
    int size() { return 1; }
    string mangle() { return "char"; }
    bool isPointerLess() { return true; }
    bool canEncode() { return true; }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("base type"[]));
      with (sect) {
        data ~= ".int\t1\t/* byte size */";
        data ~= qformat(".byte\t"[], hex(DW.ATE_signed_char), "\t/* signed char */"[]);
        data ~= dwarf2.strings.addString("char"[]);
      }
      return sect;
    }
  }
}

final class Char : Char_ { }

class Byte_ : Type, Dwarf2Encodable {
  override {
    int size() { return 1; }
    string mangle() { return "byte"; }
    bool isPointerLess() { return true; }
    bool canEncode() { return true; }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("base type"[]));
      with (sect) {
        data ~= ".int\t1\t/* byte size */";
        data ~= qformat(".byte\t"[], hex(DW.ATE_signed), "\t/* signed */"[]);
        data ~= dwarf2.strings.addString("byte"[]);
      }
      return sect;
    }
  }
}

final class Byte : Byte_ { }

const nativeIntSize = 4, nativePtrSize = 4;

final class SizeT : Type {
  override int size() { return nativeIntSize; }
  override string mangle() { return "size_t"; }
  override bool isPointerLess() { return true; }
}

final class Short : Type {
  override int size() { return 2; }
  override string mangle() { return "short"; }
  override bool isPointerLess() { return true; }
}

class SysInt_ : Type, Dwarf2Encodable {
  override int size() { return nativeIntSize; }
  override string mangle() { return "int"; }
  override bool isPointerLess() { return true; }
  override bool canEncode() { return true; }
  override Dwarf2Section encode(Dwarf2Controller dwarf2) {
    auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("base type"[]));
    with (sect) {
      data ~= ".int\t4\t/* byte size */";
      data ~= qformat(".byte\t"[], hex(DW.ATE_signed), "\t/* signed int */"[]);
      data ~= dwarf2.strings.addString("int"[]);
    }
    return sect;
  }
}

final class SysInt : SysInt_ {}

final class Long : Type {
  override int size() { return 8; }
  override string mangle() { return "long"; }
  override bool isPointerLess() { return true; }
}

class Float_ : Type, Dwarf2Encodable {
  override {
    int size() { return 4; }
    string mangle() { return "float"; }
    bool isPointerLess() { return true; }
    bool canEncode() { return true; }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("base type"[]));
      with (sect) {
        data ~= ".int\t4\t/* byte size */";
        data ~= qformat(".byte\t"[], hex(DW.ATE_float), "\t/* float */"[]);
        data ~= dwarf2.strings.addString("float"[]);
      }
      return sect;
    }
  }
}

final class Float : Float_ { }

final class Double : Type {
  override int size() { return 8; }
  override string mangle() { return "double"; }
  override bool isPointerLess() { return true; }
}

final class Real : Type {
  override int size() { return 10; }
  override string mangle() { return "real"; }
  override bool isPointerLess() { return true; }
}

// quick and dirty singleton
template _Single(T, U...) {
  T value;
  static this() { value = new T(U); }
}

template Single(T, U...) {
  static assert(is(T: Object));
  alias _Single!(T, U).value Single;
}

const string BasicTypeTable = `
  name   | type
  void   | Void
  size_t | SizeT
  int    | SysInt
  long   | Long
  short  | Short
  char   | Char
  byte   | Byte
  float  | Float
  double | Double
  real   | Real
  ...    | Variadic
`;

import parseBase, tools.ctfe: ctTableUnroll;
Object gotBasicType(ref string text, ParseCb cont, ParseCb rest) {
  mixin(BasicTypeTable.ctTableUnroll(`
    if (text.accept("$name"[])) return Single!($type);
  `));
  return null;
}
mixin DefaultParser!(gotBasicType, "type.basic"[], "2"[]);

// postfix type modifiers
IType delegate(ref string text, IType cur, ParseCb cont, ParseCb rest)[]
  typeModlist;

Object gotExtType(ref string text, ParseCb cont, ParseCb rest) {
  auto type = fastcast!(IType)~ cont(text);
  if (!type) return null;
  restart:
  foreach (dg; typeModlist) {
    if (auto nt = dg(text, type, cont, rest)) {
      type = nt;
      goto restart;
    }
  }
  return fastcast!(Object)~ type;
}
mixin DefaultParser!(gotExtType, "type.ext"[], "1"[]);

class HintType(T) : IType {
  override {
    int size() { fail; return 0; }
    int opEquals(IType other) { return !!fastcast!(T) (other); }
    string mangle() { fail; return null; }
    ubyte[] initval() { fail; return null; }
    IType proxyType() { return null; }
    bool isPointerLess() { return false; }
    bool isComplete() { return false; }
  }
}

/* used to break recursion loops on types that allow self-reference, like type alias and delegate */
Stuple!(IType, IType)[] recursestack;
int rs_size;
void pushRecurse(IType a, IType b = null) {
  if (rs_size == recursestack.length) {
    if (!recursestack.length) recursestack.length = 16;
    else recursestack.length = recursestack.length * 2;
  }
  recursestack[rs_size++] = stuple(a, b);
}
void popRecurse() {
  rs_size --;
  assert(rs_size);
}
bool alreadyRecursing(IType a, IType b = null) {
  foreach (entry; recursestack[0 .. rs_size])
    if (entry._0 is a && entry._1 is b) return true;
  return false;
}
