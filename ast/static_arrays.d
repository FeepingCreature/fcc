module ast.static_arrays;

import ast.base, ast.types, dwarf2;

class StaticArray : Type, ForceAlignment, Dwarf2Encodable {
  IType elemType;
  int length;
  this() { }
  this(IType et, int len) { elemType = et; length = len; }
  override {
    string toString() { return Format(elemType, "[", length, "] - %", alignment(), "%"); }
    int size() {
      return length * elemType.size();
    }
    int alignment() {
      if (auto fa = fastcast!(ForceAlignment) (resolveType(elemType))) return fa.alignment();
      return needsAlignment(elemType);
    }
    string mangle() {
      return Format("Static_", length, "_of_", elemType.mangle());
    }
    int opEquals(IType ty) {
      ty = resolveType(ty);
      return super.opEquals(ty) &&
        ((fastcast!(StaticArray)~ ty).elemType == elemType) &&
        ((fastcast!(StaticArray)~ ty).length == length);
    }
    bool canEncode() {
      auto d2e = fastcast!(Dwarf2Encodable)(resolveType(elemType));
      return d2e && d2e.canEncode();
    }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto elemref = registerType(dwarf2, fastcast!(Dwarf2Encodable) (resolveType(elemType)));
      auto sect = new Dwarf2Section(dwarf2.cache.getKeyFor("array type"));
      with (sect) {
        data ~= elemref;
        data ~= qformat(".4byte\t", size(), "\t/* static array size */");
      }
      return sect;
    }
  }
}

import ast.fold;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb cont, ParseCb rest) {
    auto t2 = text;
    Expr len_ex;
    if (!t2.accept("x")) return null;
    if (!rest(t2, "tree.expr _tree.expr.arith", &len_ex)) return null;
    auto backup_len = len_ex;
    if (!gotImplicitCast(len_ex, (IType it) { return test(Single!(SysInt) == it); }))
      t2.failparse("Need int for static array, not ", backup_len);
    opt(len_ex);
    auto len = foldex(len_ex);
    if (auto ie = fastcast!(IntExpr) (len)) {
      text = t2;
      return new StaticArray(cur, ie.num);
    } else
      t2.failparse("Need foldable constant for static array, not ", len);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (!fastcast!(StaticArray) (resolveType(ex.valueType()))) return null;
    ex = foldex(ex);
    if (!fastcast!(CValue) (ex))
      return null;
    return getSAPtr(ex);
  };
}

import ast.parse, ast.int_literal;
Object gotSALength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = fastcast!(StaticArray)~ ex.valueType()) {
      return mkInt(sa.length);
    } else return null;
  };
}
mixin DefaultParser!(gotSALength, "tree.rhs_partial.static_array_length", null, ".length");

Expr getSAPtr(Expr sa) {
  auto vt = fastcast!(StaticArray) (resolveType(sa.valueType()));
  assert(!!fastcast!(CValue) (sa));
  return reinterpret_cast(new Pointer(vt.elemType), new RefExpr(fastcast!(CValue) (sa)));
}

import ast.parse, ast.namespace, ast.int_literal, ast.pointer, ast.casting;
Object gotSAPointer(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = fastcast!(StaticArray)~ ex.valueType()) {
      auto cv = fastcast!(CValue)~ ex;
      if (!cv) throw new Exception(
        Format("Tried to reference non-cvalue for .ptr: ", ex)
      );
      return fastcast!(Object)~ getSAPtr(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotSAPointer, "tree.rhs_partial.static_array_ptr", null, ".ptr");

ubyte[] takeEnd(ref ubyte[] ub, int b = 1) {
  auto res = ub[$-b .. $];
  ub = ub[0..$-b];
  return res;
}

int constants_id;

// static array literal 1
class DataExpr : CValue {
  ubyte[] data;
  string name_used;
  this(ubyte[] ub) { data = ub; this(); }
  this() { }
  mixin defaultIterate!();
  override {
    DataExpr dup() { return new DataExpr(data); }
    IType valueType() { return new StaticArray(Single!(Char), data.length); }
    string toString() {
      if (data.length > 128) return Format("[byte x", data.length, "]");
      return Format(data);
    }
    void emitAsm(AsmFile af) {
      bool allNull = true;
      foreach (val; data) if (val) { allNull = false; break; }
      if (allNull) {
        /*af.flush();
        auto backup = af.optimize;
        // don't even try to opt this
        af.optimize = false;*/
        // sure?
        if (isARM) {
          int len = data.length;
          af.mmove4("#0", "r0");
          while (len) {
            if (len >= 4) {
              af.pushStack("r0", 4);
              len -= 4;
            } else if (len >= 2) {
              af.pushStack("r0", 2);
              len -= 2;
            } else {
              af.salloc(1);
              af.mmove1("r0", "[sp]");
              len --;
            }
          }
        } else {
          af.pushStack(Format("$", 0), data.length); // better optimizable
        }
        // af.flush();
        // af.optimize = backup;
        return;
      }
      auto d2 = data;
      while (d2.length >= 4) {
        auto i = (cast(int[]) d2.takeEnd(4))[0];
        if (isARM) {
          af.mmove4(Format("#", i), "r0");
          af.pushStack("r0", 4);
        } else {
          af.pushStack(Format("$", i), 4);
        }
      }
      while (d2.length) {
        auto c = d2.takeEnd();
        if (isARM) {
          af.salloc(1);
          af.mmove4(Format("#", c), "r0");
          af.mmove1("r0", "[sp]");
        } else {
          af.pushStack(Format("$", c), 1);
        }
      }
    }
    void emitLocation(AsmFile af) {
      if (!name_used) {
        name_used = af.allocConstant(Format("data_", constants_id++), data);
      }
      if (isARM) {
        af.mmove4("="~name_used, "r0");
        af.pushStack("r0", 4);
      } else {
        af.pushStack("$"~name_used, nativePtrSize);
      }
    }
  }
}

class SALiteralExpr : Expr {
  Expr[] exs;
  this() { }
  this(IType type, Expr[] exprs...) { this.type = type; exs = exprs.dup; }
  mixin DefaultDup!();
  mixin defaultIterate!(exs);
  IType type;
  override {
    IType valueType() { return new StaticArray(type, exs.length); }
    void emitAsm(AsmFile af) {
      // stack emit order: reverse!
      // TODO: Alignment.
      foreach_reverse (ex; exs)
        ex.emitAsm(af);
    }
    string toString() { return Format("SA literal ", exs); }
  }
}

extern(C) LValue ast_vardecl_lvize(Expr ex, Statement* late_init = null);

Object gotSALiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr[] exs;
  int[] statics;
  bool isStatic = true;
  IType type;
  Expr ex;
  if (!t2.bjoin(
    !!rest(t2, "tree.expr", &ex),
    t2.accept(","),
    {
      IType[] types;
      if (!type) type = ex.valueType();
      else if (!gotImplicitCast(ex, (IType it) { types ~= it; return test(it == type); }))
        t2.failparse("Invalid SA literal member; none of ", types, " match ", type);
      if (auto ie = fastcast!(IntExpr)~ fold(ex)) statics ~= ie.num;
      else isStatic = false;
      exs ~= ex;
    }
  )) t2.failparse("Failed to parse array literal");
  if (!t2.accept("]"))
    t2.failparse("Expected closing ']'");
  if (!exs.length)
    return null;
  text = t2;
  if (isStatic) {
    return fastcast!(Object)~ reinterpret_cast(fastcast!(IType)~ new StaticArray(type, exs.length), fastcast!(CValue)~ new DataExpr(cast(ubyte[]) statics));
  }
  auto res = new SALiteralExpr;
  res.type = type;
  res.exs = exs;
  Expr res_e = res;
  Statement st;
  res_e = ast_vardecl_lvize(res_e, &st); // TODO: validate if correct
  if (st) res_e = mkStatementAndExpr(st, res_e);
  return fastcast!(Object) (res_e);
}
mixin DefaultParser!(gotSALiteral, "tree.expr.literal.array", "52", "[");
