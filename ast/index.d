module ast.index;

import ast.parse, ast.base, ast.math, ast.pointer, ast.casting, ast.arrays;

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

Object gotArrayIndexAccess(ref string text, ParseCb cont, ParseCb rest) {
  auto lp = lhs_partial();
  if (cast(Expr) lp && cast(StaticArray) (cast(Expr) lp).valueType()) {
    if (!cast(LValue) lp)
      throw new Exception("LHS of array access must be lvalue for now, not "~(cast(Object) lp).toString());
    auto t2 = text;
    Expr pos;
    if (t2.accept("[") && rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      // TODO typecheck pos here
      text = t2;
      return new SA_Access!(LValue) (cast(LValue) lhs_partial(), pos);
    } else return null;
  } else return null;
}
mixin DefaultParser!(gotArrayIndexAccess, "tree.rhs_partial.array_access");

// Pointer access as array
class PA_Access : LValue {
  Expr ptr, pos;
  Expr foob, barb;
  this(Expr p, Expr o) {
    ptr = p;
    pos = o;
    foob = new AddExpr(ptr, pos);
    barb = new DerefExpr(foob);
  }
  override {
    Type valueType() { return (cast(Pointer) ptr.valueType()).target; }
    // TODO generic case
    void emitAsm(AsmFile af) {
      barb.emitAsm(af);
    }
    void emitLocation(AsmFile af) {
      foob.emitAsm(af);
    }
  }
}

Object gotPointerIndexAccess(ref string text, ParseCb cont, ParseCb rest) {
  auto lp = lhs_partial(), lpe = cast(Expr) lp;
  if (lpe && cast(Pointer) lpe.valueType()) {
    auto t2 = text;
    Expr pos;
    if (t2.accept("[") && rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      if (pos.valueType().size() != 4) throw new Exception(Format("Invalid index: ", pos));
      text = t2;
      return new PA_Access (lpe, pos);
    } else return null;
  } else return null;
}
mixin DefaultParser!(gotPointerIndexAccess, "tree.rhs_partial.pointer_index_access");
