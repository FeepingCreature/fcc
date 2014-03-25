module ast.static_arrays;

import ast.base, ast.types, dwarf2;

class StaticArray_ : Type, ForceAlignment, Dwarf2Encodable {
  IType elemType;
  int length;
  this() { }
  this(IType et, int len) { elemType = et; length = len; }
  override {
    string toString() { return Format(elemType, "["[], length, "] - %"[], "todo", "%"[]); }
    string llvmSize() { return llmul(qformat(length), elemType.llvmSize()); }
    string llvmType() { return qformat("[ ", length, " x ", typeToLLVM(elemType), " ]"); }
    int alignment() {
      if (auto fa = fastcast!(ForceAlignment) (resolveType(elemType))) return fa.alignment();
      return needsAlignment(elemType);
    }
    string mangle() {
      return Format("Static_"[], length, "_of_"[], elemType.mangle());
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
      todo("StaticArray::encode");
      return null;
      /*auto elemref = registerType(dwarf2, fastcast!(Dwarf2Encodable) (resolveType(elemType)));
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("array type"[]));
      with (sect) {
        data ~= elemref;
        data ~= qformat(".int\t"[], size(), "\t/* static array size * /"[]);
      }
      return sect;*/
    }
  }
}

final class StaticArray : StaticArray_ {
  static const isFinal = true;
  this() { }
  this(IType et, int len) { elemType = et; length = len; }
}

import ast.fold;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb cont, ParseCb rest) {
    auto t2 = text;
    Expr len_ex;
    {
      string hasToBeX;
      if (!t2.gotIdentifier(hasToBeX) || hasToBeX != "x"[]) return null;
      IType bogus;
      if (rest(t2, "type", &bogus)) return null;
    }
    if (!rest(t2, "tree.expr _tree.expr.bin"[], &len_ex)) return null;
    auto backup_len = len_ex;
    if (!gotImplicitCast(len_ex, (IType it) { return test(Single!(SysInt) == it); }))
      t2.failparse("Need int for static array, not "[], backup_len);
    auto len = collapse(len_ex);
    if (auto ie = fastcast!(IntExpr) (len)) {
      text = t2;
      return fastalloc!(StaticArray)(cur, ie.num);
    } else
      t2.failparse("Need foldable constant for static array, not "[], len);
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
mixin DefaultParser!(gotSALength, "tree.rhs_partial.static_array_length"[], null, ".length"[]);

Expr getSAPtr(Expr sa) {
  auto vt = fastcast!(StaticArray) (resolveType(sa.valueType()));
  assert(!!fastcast!(CValue) (sa));
  return reinterpret_cast(fastalloc!(Pointer)(vt.elemType), fastalloc!(RefExpr)(fastcast!(CValue) (sa)));
}

import ast.parse, ast.namespace, ast.int_literal, ast.pointer, ast.casting;
Object gotSAPointer(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (auto sa = fastcast!(StaticArray)~ ex.valueType()) {
      auto cv = fastcast!(CValue)~ ex;
      if (!cv) throw new Exception(
        Format("Tried to reference non-cvalue for .ptr: "[], ex)
      );
      return fastcast!(Object)~ getSAPtr(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotSAPointer, "tree.rhs_partial.static_array_ptr"[], null, ".ptr"[]);

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
  mixin defaultCollapse!();
  override {
    DataExpr dup() { return fastalloc!(DataExpr)(data); }
    IType valueType() { return fastalloc!(StaticArray)(Single!(UByte), data.length); }
    string toString() {
      if (data.length > 128) return Format("[byte x"[], data.length, "]"[]);
      return Format(data);
    }
    void emitLLVM(LLVMFile lf) {
      string array;
      foreach (b; data) {
        if (array) array ~= ", ";
        array ~= qformat("i8 ", b);
      }
      push(lf, "[", array, "]");
    }
    void emitLocation(LLVMFile lf) {
      if (!name_used) {
        name_used = allocConstant(lf, Format("data_"[], constants_id++), data, true);
      }
      push(lf, "@", name_used);
    }
  }
}

class SALiteralExpr : Expr {
  Expr[] exs;
  this() { }
  this(IType type, Expr[] exprs...) { this.type = type; exs = exprs.dup; }
  mixin DefaultDup!();
  mixin defaultIterate!(exs);
  mixin defaultCollapse!();
  IType type;
  override {
    IType valueType() { return fastalloc!(StaticArray)(type, exs.length); }
    void emitLLVM(LLVMFile lf) {
      auto bts = typeToLLVM(type);
      auto ars = qformat("[", exs.length, " x ", bts, "]");
      string res = "undef";
      foreach (i, ex; exs) {
        auto val = save(lf, ex);
        res = save(lf, "insertvalue ", ars, " ", res, ", ", bts, " ", val, ", ", i);
      }
      push(lf, res);
    }
    string toString() { return Format("SA literal "[], exs); }
  }
}

extern(C) LValue ast_vardecl_lvize(Expr ex, Statement* late_init = null);

Expr mkSALit(IType ty, Expr[] exs) {
  auto res = new SALiteralExpr;
  res.type = ty;
  res.exs = exs;
  // TODO: validate if correct
  Expr res_e = res;
  Statement st;
  res_e = ast_vardecl_lvize(res_e, &st);
  if (st) res_e = mkStatementAndExpr(st, res_e);
  return res_e;
}

Object gotSALiteral(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr[] exs;
  // int[] statics;
  // bool isStatic = true;
  IType type;
  Expr ex;
  if (!t2.bjoin(
    !!rest(t2, "tree.expr"[], &ex),
    t2.accept(","[]),
    {
      IType[] types;
      if (!type) type = ex.valueType();
      else if (!gotImplicitCast(ex, (IType it) { types ~= it; return test(it == type); }, false))
        t2.failparse("Invalid SA literal member; none of "[], types, " match "[], type);
      opt(ex);
      // if (auto ie = fastcast!(IntExpr) (ex)) statics ~= ie.num;
      // else isStatic = false;
      exs ~= ex;
    }
  )) t2.failparse("Failed to parse array literal"[]);
  if (!t2.accept("]"[]))
    t2.failparse("Expected closing ']'"[]);
  if (!exs.length)
    return null;
  text = t2;
  /*if (isStatic) {
    return fastcast!(Object)~ reinterpret_cast(fastcast!(IType)~ fastalloc!(StaticArray)(type, exs.length), fastcast!(CValue)~ fastalloc!(DataExpr)(cast(ubyte[]) statics));
  }*/
  return fastcast!(Object) (mkSALit(type, exs));
}
mixin DefaultParser!(gotSALiteral, "tree.expr.literal.array"[], "52"[], "["[]);
