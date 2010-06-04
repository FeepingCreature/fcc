module ast.arrays;

import ast.base, ast.types, tools.base: This, This_fn, rmSpace;

class StaticArray : Type {
  Type elemType;
  int length;
  this() { }
  this(Type et, int len) { elemType = et; length = len; }
  override int size() {
    return length * elemType.size();
  }
  override string mangle() {
    return Format("Static_", length, "_of_", elemType.mangle());
  }
}

static this() {
  typeModlist ~= delegate Type(ref string text, Type cur) {
    auto t2 = text;
    int len;
    if (t2.accept("[") &&
        t2.gotInt(len) &&
        t2.accept("]")
      )
    {
      text = t2;
      return new StaticArray(cur, len);
    } else return null;
  };
}

import ast.parse, ast.literals;
Object gotSALength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = cast(StaticArray) ex.valueType()) {
      if (!text.accept(".length")) return null;
      return new IntExpr(sa.length);
    } else return null;
  };
}
mixin DefaultParser!(gotSALength, "tree.rhs_partial.static_array_length");

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

// kind of a static array literal
class DataExpr : Expr {
  ubyte[] data;
  this(ubyte[] ub) { data = ub; }
  override Type valueType() { return new StaticArray(Single!(Char), data.length); }
  override void emitAsm(AsmFile af) {
    auto d2 = data;
    while (d2.length >= 4) {
      auto i = (cast(int[]) d2.take(4))[0];
      af.pushStack(Format("$", i), Single!(SysInt)); // TODO: use 4-byte type
    }
    while (d2.length) {
      auto c = d2.take();
      af.pushStack(Format("$", c), Single!(Char));
    }
  }
}
