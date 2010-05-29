module ast.arrays;

import ast.base, ast.types, tools.base: This, This_fn, rmSpace;

class StaticArray : Type {
  Type elemType;
  int length;
  this() { }
  mixin This!("elemType, length");
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
    StaticArray res;
    if (t2.accept("[") && (New(res), res.elemType = cur, true) &&
        t2.gotInt(res.length) &&
        t2.accept("]")
      )
    {
      text = t2;
      return res;
    } else return null;
  };
}

import ast.math, ast.pointer, ast.casting;
class SA_Access(T) : T {
  T array; Expr pos;
  Expr foob, barb;
  this(T a, Expr p) {
    array = a;
    pos = p;
    foob = new AddExpr(new ReinterpretCast!(Expr) (new Pointer((cast(StaticArray) array.valueType()).elemType), new RefExpr(cast(LValue) array)), pos);
    barb = new DerefExpr(foob);
  }
  override {
    Type valueType() { return (cast(StaticArray) array.valueType()).elemType; }
    static assert(is(T: LValue));
    // TODO generic case
    static if (is(T: LValue)) {
      void emitAsm(AsmFile af) {
        barb.emitAsm(af);
      }
      void emitLocation(AsmFile af) {
        foob.emitAsm(af);
      }
    }
  }
}

import ast.parse;
Object gotArrayAccess(ref string text, ParseCb cont, ParseCb rest) {
  auto lp = lhs_partial();
  if (cast(Expr) lp && cast(StaticArray) (cast(Expr) lp).valueType()) {
    if (!cast(LValue) lp)
      throw new Exception("LHS of array access must be lvalue for now, not "~(cast(Object) lp).toString());
    auto t2 = text;
    Expr pos;
    if (t2.accept("[") && rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      text = t2;
      return new SA_Access!(LValue) (cast(LValue) lhs_partial(), pos);
    } else return null;
  } else return null;
}
mixin DefaultParser!(gotArrayAccess, "tree.rhs_partial.array_access");
