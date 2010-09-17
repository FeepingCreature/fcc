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
    if (auto ar = cast(Array) sup.valueType()) type = ar;
    else if (auto ea = cast(ExtArray) sup.valueType()) type = new Array(ea.elemType);
    else {
      logln("full slice value type on ", sup.valueType(), " .. huh. ");
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
        
        iparse!(Statement, "fullslice_assign", "tree.semicol_stmt.assign")
               (`var = temp[0 .. temp.length]`,
                "var", var, "temp", temp).emitAsm(af);
      });
    }
  }
}

import ast.iterator, ast.casting;
Object gotSliceExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!cast(Array) ex.valueType() && !cast(ExtArray) ex.valueType() && !cast(Pointer) ex.valueType()) return null;
    auto t2 = text;
    Expr range;
    if (t2.accept("[") && t2.accept("]") || (t2 = text, true) &&
        t2.accept("[") && rest(t2, "tree.expr", &range) && t2.accept("]")
    ) {
      Expr from, to;
      if (range) {
        auto casted = new RCE((cast(Range) range.valueType()).wrapper, range);
        from = iparse!(Expr, "slice_range_from", "tree.expr")("ex.cur", "ex", casted);
        to   = iparse!(Expr, "slice_range_to",   "tree.expr")("ex.end", "ex", casted);
      }
      if (!from && !to && !cast(LValue) ex) {
        text = t2;
        return new FullSlice(ex);
      }
      if (!from) from = new IntExpr(0);
      if (!to) {
        if (!cast(Array) ex.valueType() && !cast(ExtArray) ex.valueType()) return null;
        // assert(!!cast(Array) ex.valueType(), "Cannot take \"full slice\" over pointer! ");
        to = getArrayLength(ex);
      }
      if (from.valueType().size() != 4) throw new Exception(Format("Invalid slice start: ", from));
      if (to.valueType().size() != 4) throw new Exception(Format("Invalid slice end: ", from));
      text = t2;
      if (cast(Array) ex.valueType() || cast(ExtArray) ex.valueType())
        return cast(Object) mkArraySlice(ex, from, to);
      else
        return cast(Object) mkPointerSlice(ex, from, to);
    } else return null;
  };
}
mixin DefaultParser!(gotSliceExpr, "tree.rhs_partial.slice");

Statement getSliceAssign(Expr slice, Expr array) {
  IType elemtype;
  IType[] tried;
  if (!gotImplicitCast(array, (IType it) { tried ~= it; return cast(StaticArray) it || cast(Array) it; })) {
    throw new Exception(Format("Can't assign to slice: ", array, "; none of ", tried, " fit. "));
  }
  if (auto sa = cast(StaticArray) array.valueType())
    elemtype = sa.elemType;
  else if (auto ar = cast(Array) array.valueType())
    elemtype = ar.elemType;
  else assert(false);
  
  auto fc = (cast(Function) sysmod.lookup("memcpy")).mkCall;
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
    auto ar = cast(Array) dest.valueType();
    if (!ar) return null;
    if (cast(LValue) dest) return null; // leave to normal assignment
    if (rest(t2, "tree.expr", &src)) {
      if (dest.valueType() != src.valueType()) {
        error = Format("Mismatching types in slice assignment: ", dest.valueType(), " <- ", src.valueType());
        if (cast(Array) src.valueType() || cast(ExtArray) src.valueType())
          throw new Exception(error);
        return null;
      }
      text = t2;
      // TODO: assert on size
      return cast(Object) getSliceAssign(dest, src);
    } else throw new Exception("Failed to parse slice-assignment value at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotSliceAssignment, "tree.semicol_stmt.assign_slice", "10");
