module ast.slice;

import ast.base, ast.arrays, ast.pointer, ast.opers, ast.modules, ast.fun,
  ast.structure, ast.parse, ast.int_literal, ast.static_arrays;

Expr mkPointerSlice(Expr ptr, Expr from, Expr to) {
  return new ArrayMaker(
    lookupOp("+", ptr, from),
    lookupOp("-", to, from)
  );
}

Expr mkArraySlice(Expr array, Expr from = null, Expr to = null) {
  return new ArrayMaker(
    lookupOp("+", new MemberAccess_Expr(arrayToStruct(array), "ptr"), from),
    lookupOp("-", to, from)
  );
}

class FullSlice : Expr {
  Expr sup;
  IType type;
  this(Expr ex) {
    sup = ex;
    auto svt = resolveType(sup.valueType());
    if (auto ar = cast(Array) svt) type = ar;
    else if (auto ea = cast(ExtArray) svt) type = new Array(ea.elemType);
    else {
      logln("full slice value type on ", sup.valueType(), " .. huh. ");
      asm { int 3; }
      assert(false);
    }
  }
  mixin defaultIterate!(sup);
  override {
    FullSlice dup() { return new FullSlice(sup.dup); }
    IType valueType() { return type; }
    import ast.vardecl, ast.assign;
    void emitAsm(AsmFile af) {
      mkVar(af, valueType(), true, (Variable var) {
        auto backup = af.checkptStack();
        scope(exit) af.restoreCheckptStack(backup);
        
        auto temp = new Variable(sup.valueType(), null, boffs(sup.valueType(), af.currentStackDepth));
        { auto vd = new VarDecl; vd.vars ~= temp; vd.emitAsm(af); }
        
        (new Assignment(temp, sup)).emitAsm(af);
        Expr slice;
        (new Assignment(var, mkArraySlice(temp, new IntExpr(0), foldex(getArrayLength(temp))))).emitAsm(af);
      });
    }
  }
}

static this() {
  defineOp("index", delegate Expr(Expr e1, Expr e2) {
    auto e1v = resolveType(e1.valueType()), e2v = resolveType(e2.valueType());
    if (cast(StaticArray) e1v) {
      assert(!!cast(LValue) e1);
      e1 = mkFullSlice(e1);
      e1v = resolveType(e1.valueType());
    }
    if (!cast(Array) e1v && !cast(ExtArray) e1v && !cast(Pointer) e1v)
      return null;
    auto range = cast(Range) e2v;
    if (!range) return null;
    auto casted = reinterpret_cast(range.wrapper, e2);
    auto from = foldex(mkMemberAccess(casted, "cur"));
    auto to   = foldex(mkMemberAccess(casted, "end"));
    if (from.valueType().size() != 4) throw new Exception(Format("Invalid slice start: ", from));
    if (to.valueType().size() != 4) throw new Exception(Format("Invalid slice end: ", from));
    
    if (cast(Array) e1v || cast(ExtArray) e1v)
      return mkArraySlice(e1, from, to);
    else
      return mkPointerSlice(e1, from, to);
  });
}

Expr mkFullSlice(Expr ex) {
  auto evt = resolveType(ex.valueType());
  if (auto sa = cast(StaticArray) evt) {
    auto cv = cast(CValue) ex;
    assert(!!cv);
    return mkPointerSlice(
      reinterpret_cast(new Pointer(sa.elemType), new RefExpr(cv)),
      new IntExpr(0), foldex(getArrayLength(ex))
    );
  } else return new FullSlice(ex);
}

import ast.iterator, ast.casting, ast.fold;
Object gotFullSliceExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!cast(Array) ex.valueType() && !cast(ExtArray) ex.valueType()) return null;
    auto t2 = text;
    if (!t2.accept("[]")) return null;
    text = t2;
    return cast(Object) mkFullSlice(ex);
  };
}
mixin DefaultParser!(gotFullSliceExpr, "tree.rhs_partial.full_slice");

Statement getSliceAssign(Expr slice, Expr array) {
  IType elemtype;
  IType[] tried;
  if (!gotImplicitCast(array, (IType it) { tried ~= it; return cast(StaticArray) it || cast(Array) it; })) {
    throw new Exception(Format("Can't assign to slice: ", array, "; none of ", tried, " fit. "));
  }
  auto avt = resolveType(array.valueType());
  if (auto sa = cast(StaticArray) avt)
    elemtype = sa.elemType;
  else if (auto ar = cast(Array) avt)
    elemtype = ar.elemType;
  else asm { int 3; }
  
  auto fc = (cast(Function) sysmod.lookup("memcpy2")).mkCall;
  fc.params ~= getArrayPtr(slice);
  fc.params ~= getArrayPtr(array);
  fc.params ~= lookupOp("*", getArrayLength(array), new IntExpr(elemtype.size));
  return new ExprStatement(fc);
}

import ast.namespace, tools.log;
Object gotSliceAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr dest, src;
  if (rest(t2, "tree.expr _tree.expr.arith", &dest) && t2.accept("=")) {
    auto ar = cast(Array) resolveType(dest.valueType());
    if (!ar) return null;
    if (cast(LValue) dest) return null; // leave to normal assignment
    if (rest(t2, "tree.expr", &src)) {
      if (ar != resolveType(src.valueType())) {
        auto mesg = Format("Mismatching types in slice assignment: ", dest.valueType(), " <- ", src.valueType());
        if (cast(Array) resolveType(src.valueType())
         || cast(ExtArray) resolveType(src.valueType()))
          text.failparse(mesg);
        else
          text.setError(mesg);
        return null;
      }
      text = t2;
      // TODO: assert on size
      return cast(Object) getSliceAssign(dest, src);
    } else t2.failparse("Failed to parse slice-assignment value");
  } else return null;
}
mixin DefaultParser!(gotSliceAssignment, "tree.semicol_stmt.assign_slice", "10");

static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto sa = cast(StaticArray) ex.valueType();
    if (!sa || !cast(CValue) ex) return null;
    return mkPointerSlice(
      getSAPtr(dcm(ex)),
      new IntExpr(0),
      new IntExpr(sa.length)
    );
  };
}
