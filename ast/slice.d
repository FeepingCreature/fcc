module ast.slice;

import ast.base, ast.arrays, ast.pointer, ast.opers, ast.modules, ast.fun,
  ast.structure, ast.parse, ast.int_literal, ast.static_arrays;

Expr mkPointerSlice(Expr ptr, Expr from, Expr to) {
  return fastalloc!(ArrayMaker)(
    lookupOp("+"[], ptr, from),
    lookupOp("-"[], to, from)
  );
}

Expr mkArraySlice(Expr array, Expr from = null, Expr to = null) {
  return tmpize_maybe(array, delegate Expr(Expr array) {
    return fastalloc!(ArrayMaker)(
      lookupOp("+"[], new MemberAccess_Expr(arrayToStruct(array), "ptr"[]), from),
      lookupOp("-"[], to, from)
    );
  });
}

class FullSlice : Expr {
  Expr sup;
  IType type;
  this(Expr ex) {
    sup = ex;
    auto svt = resolveType(sup.valueType());
    if (auto ar = fastcast!(Array)~ svt) type = ar;
    else if (auto ea = fastcast!(ExtArray)~ svt) type = fastalloc!(Array)(ea.elemType);
    else {
      logln("full slice value type on "[], sup.valueType(), " .. huh. "[]);
      fail;
      assert(false);
    }
  }
  mixin defaultIterate!(sup);
  override {
    FullSlice dup() { return fastalloc!(FullSlice)(sup.dup); }
    IType valueType() { return type; }
    import ast.vardecl, ast.assign;
    void emitAsm(AsmFile af) {
      mkVarUnaligned(af, valueType(), true, (Variable var) {
        auto backup = af.checkptStack();
        scope(exit) af.restoreCheckptStack(backup);
        
        auto temp = fastalloc!(Variable)(sup.valueType(), cast(string) null, sup, boffs(sup.valueType(), af.currentStackDepth));
        
        (fastalloc!(VarDecl)(temp)).emitAsm(af);
        
        emitAssign(af, var, foldex(mkArraySlice(temp, mkInt(0), getArrayLength(temp))));
      });
    }
  }
}

static this() {
  defineOp("index"[], delegate Expr(Expr e1, Expr e2) {
    auto e1v = resolveType(e1.valueType()), e2v = resolveType(e2.valueType());
    if (fastcast!(StaticArray)~ e1v) {
      if (fastcast!(LValue) (e1)) {
        e1 = mkFullSlice(e1);
        e1v = resolveType(e1.valueType());
      }
    }
    if (!fastcast!(Array) (e1v) && !fastcast!(ExtArray) (e1v) && !fastcast!(Pointer) (e1v))
      return null;
    auto rish = fastcast!(RangeIsh)~ e2v;
    if (!rish) return null;
    auto from = foldex(rish.getPos(e2));
    auto to   = foldex(rish.getEnd(e2));
    if (from.valueType().size() != 4) throw new Exception(Format("Invalid slice start: "[], from));
    if (to.valueType().size() != 4) throw new Exception(Format("Invalid slice end: "[], from));
    
    if (fastcast!(Array)~ e1v || fastcast!(ExtArray)~ e1v)
      return mkArraySlice(e1, from, to);
    else
      return mkPointerSlice(e1, from, to);
  });
}

Expr mkFullSlice(Expr ex) {
  auto evt = resolveType(ex.valueType());
  if (auto sa = fastcast!(StaticArray)~ evt) {
    auto cv = fastcast!(CValue)~ ex;
    if (!cv) {
      logln("Not a cv for full slice: "[], ex);
      fail;
    }
    return mkPointerSlice(
      reinterpret_cast(fastalloc!(Pointer)(sa.elemType), fastalloc!(RefExpr)(cv)),
      mkInt(0), foldex(getArrayLength(ex))
    );
  } else return fastalloc!(FullSlice)(ex);
}

import ast.iterator, ast.casting, ast.fold;
Object gotFullSliceExpr(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (!gotImplicitCast(ex, (IType it) { return fastcast!(Array) (it) || fastcast!(ExtArray) (it); }))
      return null;
    return fastcast!(Object) (mkFullSlice(ex));
  };
}
mixin DefaultParser!(gotFullSliceExpr, "tree.rhs_partial.full_slice"[], null, "[]"[]);

import ast.vardecl;
Statement getSliceAssign(Expr slice, Expr array) {
  IType elemtype;
  IType[] tried;
  if (!gotImplicitCast(array, (IType it) { tried ~= it; return fastcast!(StaticArray)~ it || fastcast!(Array)~ it; })) {
    throw new Exception(Format("Can't assign to slice: "[], array, "; none of "[], tried, " fit. "[]));
  }
  auto avt = resolveType(array.valueType());
  if (auto sa = fastcast!(StaticArray)~ avt)
    elemtype = sa.elemType;
  else if (auto ar = fastcast!(Array)~ avt)
    elemtype = ar.elemType;
  else fail;
  return fastalloc!(ExprStatement)(tmpize_maybe(array, delegate Expr(Expr array) {
    auto fc = (fastcast!(Function)~ sysmod.lookup("memcpy2"[])).mkCall;
    fc.params ~= getArrayPtr(slice);
    fc.params ~= getArrayPtr(array);
    fc.params ~= lookupOp("*"[], getArrayLength(array), mkInt(elemtype.size));
    return fc;
  }));
}

import ast.namespace, tools.log;
Object gotSliceAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr dest, src;
  if (rest(t2, "tree.expr _tree.expr.arith"[], &dest) && t2.accept("="[])) {
    auto ar = fastcast!(Array)~ resolveType(dest.valueType());
    if (!ar) return null;
    if (fastcast!(LValue)~ dest) return null; // leave to normal assignment
    if (rest(t2, "tree.expr"[], &src)) {
      auto t3 = t2;
      if (t3.mystripl().length && !t3.accept(";"[]))
        t2.failparse("Expected ; after slice assignment"[]);
      auto svt = resolveType(src.valueType());
      IType[] tried;
      if (!gotImplicitCast(src, (IType it) { auto rit = resolveType(it); tried ~= rit; return test(ar == rit); })) {
        auto mesg = Format("Mismatching types in slice assignment: "[], ar, " []= "[], svt, "[], tried "[], tried);
        if (fastcast!(Array)(svt)
         || fastcast!(ExtArray)(svt))
          text.failparse(mesg);
        else
          text.setError(mesg);
        return null;
      }
      text = t2;
      // TODO: assert on size
      return fastcast!(Object)~ getSliceAssign(dest, src);
    } else t2.failparse("Failed to parse slice-assignment value"[]);
  } else return null;
}
mixin DefaultParser!(gotSliceAssignment, "tree.semicol_stmt.assign_slice"[], "10"[]);

static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto sa = fastcast!(StaticArray) (ex.valueType());
    if (!sa || !fastcast!(CValue) (ex)) return null;
    return mkPointerSlice(
      getSAPtr(dcm(ex)),
      mkInt(0),
      mkInt(sa.length)
    );
  };
}
