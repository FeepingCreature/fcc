module ast.types;

import tools.base: Stuple, take;

import ast.base;

class Type {
  abstract int size();
  abstract string mangle();
  ubyte[] initval() { return new ubyte[size()]; }
  int opEquals(Object obj) {
    // specialize where needed
    return this.classinfo is obj.classinfo &&
      size == (cast(Type) cast(void*) obj).size;
  }
}

class Void : Type {
  override int size() { return 1; } // for arrays
  override string mangle() { return "void"; }
  override ubyte[] initval() { return null; }
}

class Variadic : Type {
  override int size() { assert(false); }
  /// BAH
  // TODO: redesign parameter match system to account for automatic conversions in variadics.
  override string mangle() { return "variadic"; }
  override ubyte[] initval() { assert(false); } // wtf variadic variable?
}

class Char : Type {
  override int size() { return 1; }
  override string mangle() { return "char"; }
}

const nativeIntSize = 4, nativePtrSize = 4;

class Class : Type {
  string name;
  Stuple!(Type, string)[] members;
  this(string name) { this.name = name; }
  override int size() { return nativePtrSize; }
  abstract override string mangle() { return "class"; }
}

class SizeT : Type {
  override int size() { return nativeIntSize; }
  override string mangle() { return "size_t"; }
}

class SysInt : Type {
  override int size() { return nativeIntSize; }
  override string mangle() { return "sys_int"; }
}

import parseBase;
Object gotBasicType(ref string text, ParseCb cont, ParseCb rest) {
  if (text.accept("void")) return Single!(Void);
  if (text.accept("size_t")) return Single!(SizeT);
  if (text.accept("int")) return Single!(SysInt);
  if (text.accept("char")) return Single!(Char);
  return null;
}
mixin DefaultParser!(gotBasicType, "type.basic", "5");

// postfix type modifiers
Type delegate(ref string text, Type cur, ParseCb cont, ParseCb rest)[]
  typeModlist;

Object gotExtType(ref string text, ParseCb cont, ParseCb rest) {
  auto type = cast(Type) cont(text);
  if (!type) return null;
  restart:
  foreach (dg; typeModlist) {
    if (auto nt = dg(text, type, cont, rest)) {
      type = nt;
      goto restart;
    }
  }
  return type;
}
mixin DefaultParser!(gotExtType, "type.ext", "1");
