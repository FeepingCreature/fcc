module ast.slice;

import ast.base, ast.arrays, ast.pointer, ast.opers, ast.modules, ast.fun,
  ast.structure, ast.parse, ast.int_literal, ast.static_arrays;

Expr mkPointerSlice(Expr ptr, Expr from, Expr to) {
  return fastalloc!(ArrayMaker)(
    lookupOp("+"[], ptr, from),
    lookupOp("-"[], to, from)
  );
}

Expr mkArraySlice(Expr array, Expr from, Expr to) {
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
  mixin defaultCollapse!();
  override {
    FullSlice dup() { return fastalloc!(FullSlice)(sup.dup); }
    IType valueType() { return type; }
    string toString() { return fastcast!(Object)(sup).toString()~"[]"; }
    import ast.vardecl, ast.assign;
    void emitLLVM(LLVMFile lf) {
      auto svt= sup.valueType();
      auto svts=typeToLLVM(svt);
      auto tp = alloca(lf, "1", svts);
      put(lf, "store ", svts, " ", save(lf, sup), ", ", svts, "* ", tp);
      auto temp = fastalloc!(DerefExpr)(fastalloc!(LLVMValue)(tp, fastalloc!(Pointer)(svt)));
      auto slice = mkArraySlice(temp, mkInt(0), getArrayLength(temp));
      opt(slice);
      slice.emitLLVM(lf);
    }
  }
}

void setupSlice() {
  scope(success) setupSlice2();
  defineOp("index"[], delegate Expr(Expr e1, Expr e2) {
    auto e2v = resolveType(e2.valueType());
    auto rish = fastcast!(RangeIsh)~ e2v;
    if (!rish) return null;
    
    auto e1v = resolveType(e1.valueType());
    if (fastcast!(StaticArray)~ e1v) {
      if (fastcast!(LValue) (e1)) {
        e1 = mkFullSlice(e1);
        e1v = resolveType(e1.valueType());
      }
    }
    if (!fastcast!(Array) (e1v) && !fastcast!(ExtArray) (e1v) && !fastcast!(Pointer) (e1v))
      return null;
    
    auto from = rish.getPos(e2);
    auto to   = rish.getEnd(e2);
    opt(from); opt(to);
    if (from.valueType().llvmSize() != "4") throw new Exception(Format("Invalid slice start: "[], from.valueType().llvmSize(), " ", from));
    if (to.valueType().llvmSize() != "4") throw new Exception(Format("Invalid slice end: "[], to.valueType().llvmSize(), " ", to));
    
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
    return optex(fastalloc!(ArrayMaker)(
      reinterpret_cast(fastalloc!(Pointer)(sa.elemType), fastalloc!(RefExpr)(cv)),
      getArrayLength(ex)
    ));
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
  if (!gotImplicitCast(array, (IType it) { tried ~= it; return fastcast!(StaticArray)~ it || fastcast!(Array)~ it; }, false)) {
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
    fc.params ~= reinterpret_cast(voidp, getArrayPtr(slice));
    fc.params ~= reinterpret_cast(voidp, getArrayPtr(array));
    fc.params ~= lookupOp("*"[], getArrayLength(array), llvmval(elemtype.llvmSize()));
    return fc;
  }));
}

import ast.namespace, tools.log;
Object gotSliceAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr dest, src;
  if (rest(t2, "tree.expr _tree.expr.bin"[], &dest) && t2.accept("="[])) {
    if (fastcast!(LValue)~ dest) return null; // leave to normal assignment
    auto ar = fastcast!(Array)~ resolveType(dest.valueType());
    if (!ar) return null;
    if (rest(t2, "tree.expr"[], &src)) {
      auto t3 = t2;
      if (t3.mystripl().length && !t3.accept(";"[]))
        t2.failparse("Expected ; after slice assignment"[]);
      auto svt = resolveType(src.valueType());
      IType[] tried;
      if (!gotImplicitCast(src, (IType it) { auto rit = resolveType(it); tried ~= rit; return test(ar == rit); }, false)) {
        auto mesg = Format("Mismatching types in slice assignment: ", ar, " = ", svt, ", tried ", tried);
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
mixin DefaultParser!(gotSliceAssignment, "tree.semicol_stmt.assign_slice"[], "105"[]);

void setupSlice2() {
  implicits ~= delegate Expr(Expr ex) {
    auto sa = fastcast!(StaticArray) (ex.valueType());
    if (!sa || !fastcast!(CValue) (ex)) return null;
    return fastalloc!(ArrayMaker)(
      getSAPtr(ex),
      mkInt(sa.length)
    );
  };
}
