module ast.arrays;

import ast.base, ast.types, ast.static_arrays, tools.base: This, This_fn, rmSpace;

class Array : Type {
  Type elemType;
  this() { }
  this(Type et) { elemType = et; }
  override int size() {
    return nativePtrSize + nativeIntSize;
  }
  override string mangle() {
    return "array_of_"~elemType.mangle();
  }
}

Type arrayAsStruct(Type base) {
  return new Structure(null,
    [
      // TODO: fix when int promotion is supported
      // Structure.Member("length", Single!(SizeT)),
      Structure.Member("length", Single!(SysInt)),
      Structure.Member("ptr", new Pointer(base))
    ]
  );
}

T arrayToStruct(T)(T array) {
  return new ReinterpretCast!(T) (arrayAsStruct((cast(Array) array.valueType()).elemType), array);
}

import ast.structure;
static this() {
  typeModlist ~= delegate Type(ref string text, Type cur, ParseCb, ParseCb) {
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
    Type valueType() {
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
  Expr ptr, length;
  mixin This!("ptr, length");
  mixin defaultIterate!(ptr, length);
  Type elemType() {
    return (cast(Pointer) ptr.valueType()).target;
  }
  override Type valueType() {
    return new Array(elemType());
  }
  import ast.vardecl, ast.assign;
  override void emitAsm(AsmFile af) {
    af.comment("start constructing array");
    mkVar(af, arrayAsStruct(elemType()), true, (Variable var) {
      af.comment("setting ptr");
      (new Assignment((new MemberAccess_LValue(var, "ptr")), ptr)).emitAsm(af);
      af.comment("setting length");
      (new Assignment((new MemberAccess_LValue(var, "length")), length)).emitAsm(af);
    });
    af.comment("done constructing array");
  }
}

Object gotStaticArrayCValAsDynamic(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto ex = cast(Expr) rest(t2, "tree.expr ^selfrule",
    delegate bool(Expr ex) {
      return cast(StaticArray) ex.valueType() && cast(CValue) ex;
    }
  );
  if (!ex) return null;
  text = t2;
  return new ArrayMaker(new CValueAsPointer(cast(CValue) ex), new IntExpr((cast(StaticArray) ex.valueType()).length));
}
mixin DefaultParser!(gotStaticArrayCValAsDynamic, "tree.expr.sa_cval_dynamic", "905");

import tools.log;
import ast.parse, ast.literals;
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

Object gotArrayPtr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = cast(Array) ex.valueType()) {
      if (!text.accept(".ptr")) return null;
      if (auto lv = cast(LValue) ex) return new MemberAccess_LValue(arrayToStruct(lv), "ptr");
      else return new MemberAccess_Expr(arrayToStruct(ex), "ptr");
    } else return null;
  };
}
mixin DefaultParser!(gotArrayPtr, "tree.rhs_partial.array_ptr");
