module ast.arrays;

import ast.base, ast.types, ast.static_arrays, tools.base: This, This_fn, rmSpace;

// ptr, length, capacity
class Array : Type {
  IType elemType;
  this() { }
  this(IType et) { elemType = et; }
  override int size() {
    return nativePtrSize + nativeIntSize * 2;
  }
  override string mangle() {
    return "array_of_"~elemType.mangle();
  }
}

IType arrayAsStruct(IType base) {
  auto res = new Structure(null);
  // TODO: fix when int promotion is supported
  // Structure.Member("length", Single!(SizeT)),
  new RelMember("capacity", Single!(SysInt), res);
  new RelMember("length", Single!(SysInt), res);
  new RelMember("ptr", new Pointer(base), res);
  return res;
}

T arrayToStruct(T)(T array) {
  return new ReinterpretCast!(T) (
    arrayAsStruct((cast(Array) array.valueType()).elemType),
    array
  );
}

import ast.structure;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    if (text.accept("[]")) {
      return new Array(cur);
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
  mixin defaultIterate!(array);
  override {
    IType valueType() {
      return Single!(SizeT);
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
  Expr ptr, length, cap;
  mixin This!("ptr, length, cap");
  mixin defaultIterate!(ptr, length, cap);
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
    cap.emitAsm(af);
  }
}

import ast.literals;
Object gotStaticArrayCValAsDynamic(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto ex = cast(Expr) rest(t2, "tree.expr ^selfrule",
    delegate bool(Expr ex) {
      return cast(StaticArray) ex.valueType() && cast(CValue) ex;
    }
  );
  if (!ex) return null;
  text = t2;
  return new ArrayMaker(
    new CValueAsPointer(cast(CValue) ex),
    new IntExpr((cast(StaticArray) ex.valueType()).length),
    new IntExpr(0)
  );
}
mixin DefaultParser!(gotStaticArrayCValAsDynamic, "tree.expr.sa_cval_dynamic", "905");

import ast.parse;
// separate because does clever allocation mojo .. eventually
Object gotArrayLength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = cast(Array) ex.valueType()) {
      if (!text.accept(".length")) return null;
      if (auto lv = cast(LValue) ex) return new ArrayLength!(MValue) (lv);
      else return new ArrayLength!(Expr) (ex);
    } else return null;
  };
}
mixin DefaultParser!(gotArrayLength, "tree.rhs_partial.array_length");


Object gotArrayAsStruct(ref string st, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (!rest(st, "tree.expr ^selfrule", &ex))
    return null;
  if (!cast(Array) ex.valueType())
    return null;
  if (auto lv = cast(LValue) ex)
    return cast(Object) arrayToStruct!(LValue) (lv);
  else
    return cast(Object) arrayToStruct!(Expr) (ex);
}
mixin DefaultParser!(gotArrayAsStruct, "tree.expr.array_struct", "915");
