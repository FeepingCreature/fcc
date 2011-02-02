module ast.index;

import ast.parse, ast.base, ast.opers, ast.pointer, ast.casting,
  ast.static_arrays, ast.arrays, ast.namespace;

import ast.iterator: RangeIsh;
LValue getIndex(Expr array, Expr pos) {
  Expr ptr;
  if (auto sa = fastcast!(StaticArray)~ array.valueType())
    ptr = getSAPtr(array);
  else
    ptr = getArrayPtr(array);
  return new DerefExpr(lookupOp("+", ptr, pos));
}

class SAIndexExpr : Expr {
  Expr ex, pos;
  this(Expr ex, Expr pos) { this.ex = ex; this.pos = pos; }
  mixin defaultIterate!(ex, pos);
  override {
    string toString() { return Format(ex, "[", pos, "]"); }
    SAIndexExpr dup() { return new SAIndexExpr(ex.dup, pos.dup); }
    IType valueType() { return (fastcast!(StaticArray)~ ex.valueType()).elemType; }
    import ast.vardecl, ast.assign;
    void emitAsm(AsmFile af) {
      mkVar(af, valueType(), true, (Variable var) {
        auto v2 = new Variable(ex.valueType(), null, boffs(ex.valueType(), af.currentStackDepth));
        ex.emitAsm(af);
        (new Assignment(var, getIndex(v2, pos))).emitAsm(af);
        af.sfree(ex.valueType().size);
      });
    }
  }
}

import ast.tuples, ast.tuple_access;
static this() {
  defineOp("index", delegate Expr(Expr e1, Expr e2) {
    auto e1v = resolveType(e1.valueType()), e2v = resolveType(e2.valueType());
    if (!fastcast!(StaticArray) (e1v) && !fastcast!(Array) (e1v) && !fastcast!(ExtArray) (e1v) && !fastcast!(Pointer) (e1v))
      return null;
    IType[] tried;
    if (!gotImplicitCast(e2, (IType it) { tried ~= it; return !!(it == Single!(SysInt)); }))
      return null;
    if (auto dcme = fastcast!(DontCastMeExpr) (e2)) e2 = dcme.sup;
    if (fastcast!(StaticArray) (e1v) && !fastcast!(CValue) (e1)) {
      return new SAIndexExpr(e1, e2);
    }
    if (fastcast!(Pointer)~ e1v)
      return new DerefExpr(lookupOp("+", e1, e2));
    return getIndex(e1, e2);
  });
  defineOp("index", delegate Expr(Expr e1, Expr e2) {
    auto e1v = resolveType(e1.valueType()), e2v = resolveType(e2.valueType());
    if (!fastcast!(StaticArray) (e1v) && !fastcast!(Array) (e1v) && !fastcast!(ExtArray) (e1v) && !fastcast!(Pointer) (e1v))
      return null;
    auto tup = fastcast!(Tuple)~ e2v;
    if (!tup) return null;
    Expr[] exprs;
    foreach (entry; getTupleEntries(e2)) exprs ~= lookupOp("index", e1, entry);
    return mkTupleExpr(exprs);
  });
}

Object gotArrayAccess(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    // logln("access ", ex.valueType(), " @", text.nextText());
    auto exv = resolveType(ex.valueType());
    if (!fastcast!(Array) (exv) && !fastcast!(ExtArray) (exv) && !fastcast!(StaticArray) (exv) && !fastcast!(Pointer) (exv))
      return null;
    auto t2 = text;
    Expr pos;
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(new LengthOverride(backup, getArrayLength(ex)));
    
    if (rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      auto res = lookupOp("index", ex, pos);
      if (!res) {
        text.failparse("Invalid array index: ", pos.valueType());
      }
      text = t2;
      return fastcast!(Object)~ res;
    } else return null;
  };
}
mixin DefaultParser!(gotArrayAccess, "tree.rhs_partial.array_access", null, "[");

// Pointer access as array
class PA_Access : LValue {
  Expr ptr, pos;
  mixin MyThis!("ptr, pos");
  mixin DefaultDup!();
  mixin defaultIterate!(ptr, pos);
  override {
    string toString() { return Format(ptr, "[", pos, "]"); }
    IType valueType() { return (fastcast!(Pointer)~ ptr.valueType()).target; }
    // TODO generic case
    void emitAsm(AsmFile af) {
      (new DerefExpr(lookupOp("+", ptr, pos))).emitAsm(af);
    }
    void emitLocation(AsmFile af) {
      (lookupOp("+", ptr, pos)).emitAsm(af);
    }
  }
}

Object gotPointerIndexAccess(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!fastcast!(Pointer) (ex.valueType())) return null;
    auto t2 = text;
    Expr pos;
    
    if (rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      if (fastcast!(RangeIsh)~ pos.valueType()) return null; // belongs to slice
      if (pos.valueType().size() != 4) throw new Exception(Format("Invalid index: ", pos));
      text = t2;
      return new PA_Access (ex, pos);
    } else return null;
  };
}
mixin DefaultParser!(gotPointerIndexAccess, "tree.rhs_partial.pointer_index_access", null, "[");
