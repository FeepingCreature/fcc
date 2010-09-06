module ast.arrays;

import ast.base, ast.types, ast.static_arrays, tools.base: This, This_fn, rmSpace;

// ptr, length
class Array : Type {
  IType elemType;
  this() { }
  this(IType et) { elemType = et; }
  override {
    int size() {
      return nativePtrSize + nativeIntSize;
    }
    string mangle() {
      return "array_of_"~elemType.mangle();
    }
    string toString() { return Format(elemType, "[]"); }
  }
}

// ptr, length, capacity
class ExtArray : Type {
  IType elemType;
  this() { }
  this(IType et) { elemType = et; }
  override {
    int size() {
      return nativePtrSize + nativeIntSize * 2;
    }
    string mangle() {
      return "rich_array_of_"~elemType.mangle();
    }
  }
}

IType arrayAsStruct(IType base, bool rich) {
  auto res = new Structure(null);
  if (rich)
    new RelMember("capacity", Single!(SysInt), res);
  // TODO: fix when int promotion is supported
  // Structure.Member("length", Single!(SizeT)),
  new RelMember("length", Single!(SysInt), res);
  new RelMember("ptr", new Pointer(base), res);
  return res;
}

T arrayToStruct(T)(T array) {
  auto
    ar = cast(Array) array.valueType(),
    ea = cast(ExtArray) array.valueType();
  if (ar)
    return new ReinterpretCast!(T) (arrayAsStruct(ar.elemType, false), array);
  if (ea)
    return new ReinterpretCast!(T) (arrayAsStruct(ea.elemType, true),  array);
  assert(false);
}

import ast.structure;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    if (text.accept("[]")) {
      return new Array(cur);
    } else if (text.accept("[~]")) {
      return new ExtArray(cur);
    } else return null;
  };
}

import ast.pointer, ast.casting;
class ArrayLength(T) : T {
  static if (is(T == MValue)) {
    alias LValue AT;
  } else {
    alias Expr AT;
  }
  AT array;
  this(AT at) {
    array = at;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(array);
  override {
    string toString() { return Format("length(", array, ")"); }
    IType valueType() {
      return Single!(SysInt); // TODO: size_t when unsigned conversion works
    }
    void emitAsm(AsmFile af) {
      (new MemberAccess_Expr(arrayToStruct(array), "length")).emitAsm(af);
    }
    static if (is(T == MValue)) void emitAssignment(AsmFile af) {
      assert(false, "TODO");
    }
  }
}

// construct array from two expressions
class ArrayMaker : Expr {
  Expr ptr, length;
  mixin MyThis!("ptr, length");
  mixin DefaultDup!();
  mixin defaultIterate!(ptr, length);
  IType elemType() {
    return (cast(Pointer) ptr.valueType()).target;
  }
  override string toString() { return Format("array(ptr=", ptr, ", length=", length, ")"); }
  override IType valueType() {
    return new Array(elemType());
  }
  import ast.vardecl, ast.assign;
  override void emitAsm(AsmFile af) {
    // TODO: stack direction/order
    ptr.emitAsm(af);
    length.emitAsm(af);
  }
}

Expr staticToArray(Expr sa) {
  return new ArrayMaker(
    new CValueAsPointer(cast(CValue) sa),
    new IntExpr((cast(StaticArray) sa.valueType()).length)
  );
}

import ast.literals, ast.casting;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (!cast(StaticArray) ex.valueType() || !cast(CValue) ex)
      return null;
    return staticToArray(ex);
  };
}

Expr getArrayLength(Expr ex) {
  if (auto lv = cast(LValue) ex) return new ArrayLength!(MValue) (lv);
  else return new ArrayLength!(Expr) (ex);
}

Expr getArrayPtr(Expr ex) {
  return mkMemberAccess(arrayToStruct!(Expr) (ex), "ptr");
}

import ast.parse;
// separate because does clever allocation mojo .. eventually
Object gotArrayLength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto ar = cast(Array) ex.valueType()) {
      if (!text.accept(".length")) return null;
      return cast(Object) getArrayLength(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotArrayLength, "tree.rhs_partial.array_length");

import ast.casting;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (!cast(Array) ex.valueType()) return null;
    if (auto lv = cast(LValue) ex)
      return arrayToStruct!(LValue) (lv);
    else
      return arrayToStruct!(Expr) (ex);
  };
}
