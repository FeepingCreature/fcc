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

import ast.structure;
static this() {
  typeModlist ~= delegate Type(ref string text, Type cur) {
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
  Expr len_expr;
  this(AT at) {
    array = at;
    len_expr = new MemberAccess!(Expr) (new ReinterpretCast!(Expr) (arrayAsStruct(Single!(Void)), array), "length");
  }
  override {
    Type valueType() {
      return Single!(SizeT);
    }
    void emitAsm(AsmFile af) {
      len_expr.emitAsm(af);
    }
    static if (is(T == MValue)) void emitAssignment(AsmFile af) {
      assert(false, "TODO");
    }
  }
}

class SA_CVal_AsDynamic : Expr {
  Expr sa;
  this(Expr e) { sa = e; }
  import ast.vardecl, ast.assign;
  Type elemType() {
    return (cast(StaticArray) sa.valueType()).elemType;
  }
  override Type valueType() {
    return new Array(elemType());
  }
  override void emitAsm(AsmFile af) {
    auto cv = cast(CValue) sa;
    af.comment("start converting cval to dynamic");
    // so it's like we're declaring an array-like struct ..
    mkVar(af, arrayAsStruct(elemType()), true, (Variable var) {
      // then assign our static pointer to ptr ..
      af.comment("setting ptr");
      (new Assignment((new MemberAccess_LValue(var, "ptr")),
                      new CValueAsPointer(cv))).emitAsm(af);
      af.comment("setting length");
      // and our known length to length.
      (new Assignment((new MemberAccess_LValue(var, "length")),
                      new IntExpr((cast(StaticArray) sa.valueType()).length))).emitAsm(af);
    });
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
  return new SA_CVal_AsDynamic(ex);
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
