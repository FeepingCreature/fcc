module ast.arrays;

import ast.base, ast.types, tools.base: This, This_fn, rmSpace;

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
    static if (is(AT == LValue)) {
      len_expr = new DerefExpr(new ReinterpretCast!(Expr) (new Pointer(Single!(SizeT)), new RefExpr(array)));
    } else {
      assert(false, "TODO");
    }
  }
  override {
    Type valueType() {
      static if (is(AT == LValue)) {
        return len_expr.valueType();
      } else {
        assert(false, "TODO");
      }
    }
    void emitAsm(AsmFile af) {
      static if (is(AT == LValue)) {
        len_expr.emitAsm(af);
      } else {
        assert(false, "TODO");
      }
    }
    static if (is(T == MValue)) void emitAssignment(AsmFile af) {
      assert(false, "TODO");
    }
  }
}

import tools.log;
import ast.parse, ast.literals;
Object gotArrayLength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    logln("checking on ", text.next_text(), ": lhs ", ex);
    if (auto sa = cast(Array) ex.valueType()) {
      if (!text.accept(".length")) return null;
      if (auto lv = cast(LValue) ex) return new ArrayLength!(MValue) (lv);
      else return new ArrayLength!(Expr) (ex);
    } else return null;
  };
}
mixin DefaultParser!(gotArrayLength, "tree.rhs_partial.array_length");
