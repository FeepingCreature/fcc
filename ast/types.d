module ast.types;

import tools.base: Stuple, take;

import ast.base;

class Type {
  int size;
  abstract string mangle();
  int opEquals(Object obj) {
    // specialize where needed
    return this.classinfo is obj.classinfo &&
      size == (cast(Type) cast(void*) obj).size;
  }
  void match(ref Expr[] params) {
    if (!params.length)
      throw new Exception(Format("Missing parameter of ", this));
    if (params[0].valueType() != this)
      throw new Exception(Format("Expected ", this, ", got ", params[0], " of ", params));
    params.take();
  }
}

class Void : Type {
  this() { size = 4; }
  override string mangle() { return "void"; }
}

class Variadic : Type {
  this() { size = 0; }
  void match(ref Expr[] params) {
    params = null; // match all
  }
  override string mangle() { return "variadic"; }
}

class Char : Type {
  this() { size = 1; }
  override string mangle() { return "char"; }
}

const nativeIntSize = 4, nativePtrSize = 4;

class Class : Type {
  string name;
  Stuple!(Type, string)[] members;
  this(string name) { this.name = name; size = nativePtrSize; }
  abstract override string mangle() { return "class"; }
}

class SizeT : Type {
  this() { size = nativeIntSize; }
  override string mangle() { return "size_t"; }
}

class SysInt : Type {
  this() { size = nativeIntSize; }
  override string mangle() { return "sys_int"; }
}

// postfix type modifiers
Type delegate(ref string text, Type cur)[] typeModlist;

import parseBase;
Object gotBasicType(ref string text, ParseCb cont, ParseCb rest) {
  if (text.accept("void")) return Single!(Void);
  if (text.accept("size_t")) return Single!(SizeT);
  if (text.accept("int")) return Single!(SysInt);
  return null;
}
mixin DefaultParser!(gotBasicType, "type.basic", "5");

Object gotExtType(ref string text, ParseCb cont, ParseCb rest) {
  auto type = cast(Type) cont(text);
  if (!type) return null;
  restart:
  foreach (dg; typeModlist) {
    if (auto nt = dg(text, type)) {
      type = nt;
      goto restart;
    }
  }
  return type;
}
mixin DefaultParser!(gotExtType, "type.ext", "1");
