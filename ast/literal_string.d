module ast.literal_string;

import ast.base, ast.literals, ast.pointer, ast.arrays, ast.static_arrays, ast.stringparse;

class StringExpr : Expr, HasInfo, Dependency {
  string str;
  bool generated;
  this() { }
  this(string s, bool g = true) { str = s; generated = g; this(); }
  mixin defaultIterate!();
  mixin defaultCollapse!();
  string name_used;
  void selectName(LLVMFile lf) {
    if (!name_used) {
      name_used = lf.allocData(qformat("string_constant_", str.length), cast(ubyte[]) str ~ cast(ubyte) 0);
    }
  }
  Expr getPointer() {
    return reinterpret_cast(Single!(Pointer, Single!(Char)),
      fastalloc!(LateSymbol)(this, fastalloc!(Pointer)(fastalloc!(StaticArray)(Single!(Char), str.length + 1)), &emitDependency, &name_used));
  }
  override {
    string getInfo() { return "'"~toString()[1 .. $-1]~"'"; }
    StringExpr dup() { return fastalloc!(StringExpr)(str, generated); }
    string toString() { return '"'~str.replace("\n"[], "\\n"[])~'"'; }
    // default action: place in string segment, load address on stack
    void emitLLVM(LLVMFile lf) {
      scope sa = new StaticArray(Single!(Char), str.length + 1);
      scope pt = new Pointer(sa);
      scope ls = new LateSymbol(this, pt, &emitDependency, &name_used);
      scope p = reinterpret_cast(Single!(Pointer, Single!(Char)), ls);
      // auto p = getPointer();
      formTuple(lf, "i32", qformat(str.length), typeToLLVM(p.valueType()), save(lf, p));
    }
    void emitDependency(LLVMFile lf) {
      if (!name_used) selectName(lf);
      else lf.allocData(name_used, cast(ubyte[]) str~ cast(ubyte) 0, false);
      // lf.markWeak(name_used);
    }
    // IType valueType() { return fastalloc!(StaticArray)(Single!(Char), str.length); }
    IType valueType() { return Single!(Array, Single!(Char)); }
  }
}

static this() {
  mkString = delegate Expr(string s) { return fastalloc!(StringExpr)(s); };
  constantStringsCompare = delegate bool(Expr e1, Expr e2, bool* bp) {
    auto se1 = fastcast!(StringExpr) (e1), se2 = fastcast!(StringExpr) (e2);
    if (!se1 || !se2) return false;
    *bp = se1.str == se2.str;
    return true;
  };
}

Object gotStringLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  // "" handled in ast.stringex now.
  string st;
  if (text.gotString(st, "`"[], true)) {
    return fastalloc!(StringExpr)(st, false);
  } else return null;
}
mixin DefaultParser!(gotStringLiteralExpr, "tree.expr.literal_string"[], "551"[], "`"[]);

import ast.casting, ast.fold, ast.math;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (resolveType(ex.valueType()) != Single!(Array, Single!(Char)))
      return null;
    opt(ex);
    if (fastcast!(StringExpr) (ex)) {
      return getArrayPtr(ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (resolveType(ex.valueType()) != Single!(Array, Single!(Char)))
      return null;
    if (auto str = fastcast!(StringExpr) (ex)) {
      if (!str.generated && str.str.length == 1)
        return reinterpret_cast(Single!(Char), fastalloc!(IntLiteralAsByte)(fastalloc!(IntExpr)(str.str[0])));
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (resolveType(ex.valueType()) != Single!(Char))
      return null;
    return reinterpret_cast(Single!(Byte), ex);
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto al = fastcast!(ArrayLength_Base)(it)) {
      opt(al.array);
      if (auto se = fastcast!(StringExpr) (al.array)) {
        return mkInt(se.str.length);
      }
    }
    return null;
  };
}
