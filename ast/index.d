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
    /*if (!gotImplicitCast(e1, (IType it) {
      it = resolveType(it);
      return fastcast!(StaticArray) (it) || fastcast!(Array) (it) || fastcast!(ExtArray) (it) || fastcast!(Pointer) (it);
    }))
      return null;*/
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
    auto tup = fastcast!(Tuple) (e2v);
    if (!tup) return null;
    Expr[] exprs;
    foreach (entry; getTupleEntries(e2)) {
      exprs ~= lookupOp("index", e1, entry);
    }
    return mkTupleExpr(exprs);
  });
}

import ast.fold;
Expr tmpize(Expr ex) {
  if (fastcast!(PlaceholderToken) (ex)) return ex;
  if (fastcast!(Variable) (ex)) return ex;
  ex = foldex(ex);
  if (fastcast!(IntExpr) (ex)) return ex;
  Statement init;
  if (auto lv = fastcast!(LValue) (ex))
    ex = new DerefExpr(lvize(new RefExpr(lv), &init));
  else
    ex = lvize(ex, &init);
  ex = mkStatementAndExpr(init, ex, true);
  return ex;
}

import ast.vardecl, ast.scopes, ast.literals;
Object gotArrayAccess(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    // logln("access ", ex.valueType(), " @", text.nextText());
    bool isArrayOrPtr = true;
    {
      auto backup = ex;
      if (!gotImplicitCast(ex, (IType it) {
        it = resolveType(it);
        return fastcast!(StaticArray) (it) || fastcast!(Array) (it) || fastcast!(ExtArray) (it) || fastcast!(Pointer) (it);
      })) {
        ex = backup; // still fine - maybe opIndex will work
        isArrayOrPtr = false;
      }
    }
    
    auto exv = resolveType(ex.valueType());
    
    auto t2 = text;
    Expr pos;
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    if (isArrayOrPtr)
      namespace.set(new LengthOverride(backup, getArrayLength(ex)));
    
    if (t2.accept("]")) return null; // [] shortcut
    if (rest(t2, "tree.expr", &pos) && t2.accept("]")) {
      Expr res;
      try {
        res = lookupOp("index", true, ex, pos);
        if (!res) {
          text.failparse("Invalid array index: ", pos.valueType());
        }
        auto posvt = pos.valueType();
        bool hasScope = !!namespace().get!(Scope);
        if (isArrayOrPtr && !fastcast!(Pointer) (ex.valueType()) && !releaseMode && hasScope && fastcast!(SysInt)(posvt)) {
          ex = tmpize(ex);
          
          pos = tmpize(pos);
          
          res = lookupOp("index", true, ex, pos);
          auto errorpos = lookupPos(text);
          string info = Format(errorpos._2, ":", errorpos._0, ":", errorpos._1);
          res = mkStatementAndExpr(
            iparse!(Statement, "check_bound", "tree.stmt")
                    (`if (pos >= ex.length) raise-error new BoundsError "Index access out of bounds: $pos >= length $(ex.length) at $info";`,
                    "pos", pos, "ex", ex, "info", mkString(info)),
            res,
            true
          );
        }
        text = t2;
      } catch (Exception ex) text.failparse(ex);
      return fastcast!(Object) (res);
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
