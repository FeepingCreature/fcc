module ast.index;

import ast.parse, ast.base, ast.math, ast.pointer, ast.casting, ast.static_arrays;

class SA_Access(T) : T {
  T array; Expr pos;
  mixin This!("array, pos");
  mixin defaultIterate!(array, pos);
  override {
    IType valueType() { return (cast(StaticArray) array.valueType()).elemType; }
    static assert(is(T: LValue));
    // TODO generic case
    static if (is(T: LValue)) {
      void emitAsm(AsmFile af) {
        (new DerefExpr(new RefExpr(this))).emitAsm(af);
      }
      void emitLocation(AsmFile af) {
        (new AddExpr(new ReinterpretCast!(Expr) (new Pointer((cast(StaticArray) array.valueType()).elemType), new RefExpr(cast(LValue) array)), pos)).emitAsm(af);
      }
    }
  }
}

Object gotArrayIndexAccess(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!cast(StaticArray) ex.valueType())
      return null;
    auto t2 = text;
    Expr pos;
    if (t2.accept("[") && rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      if (!cast(LValue) ex)
        throw new Exception("LHS of array access must be lvalue for now, not "~(cast(Object) ex).toString());
      // TODO typecheck pos here
      text = t2;
      return new SA_Access!(LValue) (cast(LValue) ex, pos);
    } else return null;
  };
}
mixin DefaultParser!(gotArrayIndexAccess, "tree.rhs_partial.array_access");

// Pointer access as array
class PA_Access : LValue {
  Expr ptr, pos;
  mixin This!("ptr, pos");
  mixin defaultIterate!(ptr, pos);
  override {
    IType valueType() { return (cast(Pointer) ptr.valueType()).target; }
    // TODO generic case
    void emitAsm(AsmFile af) {
      (new DerefExpr(new AddExpr(ptr, pos))).emitAsm(af);
    }
    void emitLocation(AsmFile af) {
      (new AddExpr(ptr, pos)).emitAsm(af);
    }
  }
}

Object gotPointerIndexAccess(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!cast(Pointer) ex.valueType()) return null;
    auto t2 = text;
    Expr pos;
    if (t2.accept("[") && rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      if (pos.valueType().size() != 4) throw new Exception(Format("Invalid index: ", pos));
      text = t2;
      return new PA_Access (ex, pos);
    } else return null;
  };
}
mixin DefaultParser!(gotPointerIndexAccess, "tree.rhs_partial.pointer_index_access");
