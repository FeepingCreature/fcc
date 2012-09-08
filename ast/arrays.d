module ast.arrays;

import ast.base, ast.types, ast.static_arrays, ast.returns, tools.base: This, This_fn, rmSpace;

import dwarf2;
// ptr, length
class Array_ : Type, RelNamespace, Dwarf2Encodable {
  IType elemType;
  this() { }
  this(IType et) { elemType = forcedConvert(et); }
  override {
    // bool isComplete() { return elemType.isComplete; }
    bool isComplete() { return true; /* size not determined by element size! */ }
    IType proxyType() { if (auto ep = elemType.proxyType()) return new Array(ep); return null; }
    int size() {
      return nativePtrSize + nativeIntSize;
    }
    bool isTempNamespace() { return false; }
    Object lookupRel(string str, Expr base, bool isDirectLookup = true) {
      int idx;
      if (readIndexShorthand(str, idx))
        return fastcast!(Object) (lookupOp("index"[], base, mkInt(idx)));
      return null;
    }
    string mangle() {
      return "array_of_"~elemType.mangle();
    }
    string toString() { return Format(elemType, "[]"[]); }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      ty = resolveType(ty);
      return (fastcast!(Array) (ty)).elemType == elemType;
    }
    bool isPointerLess() { return false; }
    bool canEncode() {
      auto d2e = fastcast!(Dwarf2Encodable)(resolveType(elemType));
      return d2e && d2e.canEncode();
    }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto elempref = registerType(dwarf2, fastcast!(Dwarf2Encodable) (fastalloc!(Pointer)(resolveType(elemType))));
      auto sizeref = registerType(dwarf2, Single!(SysInt));
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("structure type"[]));
      with (sect) {
        data ~= ".int\t8\t/* byte size */";
        auto len = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("structure member"[]));
        with (len) {
          data ~= dwarf2.strings.addString("length"[]);
          data ~= sizeref;
          data ~= ".byte\t1f - 0f\t/* size */";
          data ~= "0:";
          data ~= ".byte\t0x23\t/* DW_OP_plus_uconst */";
          data ~= ".uleb128\t0x0\t/* offset */";
          data ~= "1:";
        }
        sub ~= len;
        auto ptr = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("structure member"[]));
        with (ptr) {
          data ~= dwarf2.strings.addString("ptr"[]);
          data ~= elempref;
          data ~= ".byte\t1f - 0f\t/* size */";
          data ~= "0:";
          data ~= ".byte\t0x23\t/* DW_OP_plus_uconst */";
          data ~= ".uleb128\t0x4\t/* offset */";
          data ~= "1:";
        }
        sub ~= ptr;
      }
      return sect;
    }
  }
}

final class Array : Array_ {
  this() { super(); }
  this(IType it) { super(it); }
}

// ptr, length, capacity
class ExtArray : Type, RelNamespace, Dwarf2Encodable {
  IType elemType;
  bool freeOnResize;
  this() { }
  this(IType et, bool fOR) { elemType = forcedConvert(et); freeOnResize = fOR; }
  override {
    bool isTempNamespace() { return false; }
    IType proxyType() { if (auto ep = elemType.proxyType()) return new ExtArray(ep, freeOnResize); return null; }
    Object lookupRel(string str, Expr base, bool isDirectLookup = true) {
      int idx;
      if (readIndexShorthand(str, idx))
        return fastcast!(Object) (lookupOp("index"[], base, mkInt(idx)));
      return null;
    }
    int size() {
      return nativePtrSize + nativeIntSize * 2;
    }
    string mangle() {
      return qformat("rich_"[], freeOnResize?"auto_"[]:null, "array_of_"[], elemType.mangle());
    }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      ty = resolveType(ty);
      auto ea = fastcast!(ExtArray) (ty);
      return ea.elemType == elemType && ea.freeOnResize == freeOnResize;
    }
    string toString() {
      return Format(elemType, "["[], freeOnResize?"auto ":""[], "~]"[]);
    }
    // copypaste from above :D
    bool canEncode() {
      auto d2e = fastcast!(Dwarf2Encodable)(resolveType(elemType));
      return d2e && d2e.canEncode();
    }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto elempref = registerType(dwarf2, fastcast!(Dwarf2Encodable) (fastalloc!(Pointer)(resolveType(elemType))));
      auto sizeref = registerType(dwarf2, Single!(SysInt));
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("structure type"[]));
      with (sect) {
        data ~= ".int\t12\t/* byte size */";
        auto cap = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("structure member"[]));
        with (cap) {
          data ~= dwarf2.strings.addString("capacity"[]);
          data ~= sizeref;
          data ~= ".byte\t1f - 0f\t/* size */";
          data ~= "0:";
          data ~= ".byte\t0x23\t/* DW_OP_plus_uconst */";
          data ~= ".uleb128\t0x0\t/* offset */";
          data ~= "1:";
        }
        sub ~= cap;
        auto len = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("structure member"[]));
        with (len) {
          data ~= dwarf2.strings.addString("length"[]);
          data ~= sizeref;
          data ~= ".byte\t1f - 0f\t/* size */";
          data ~= "0:";
          data ~= ".byte\t0x23\t/* DW_OP_plus_uconst */";
          data ~= ".uleb128\t0x4\t/* offset */";
          data ~= "1:";
        }
        sub ~= len;
        auto ptr = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("structure member"[]));
        with (ptr) {
          data ~= dwarf2.strings.addString("ptr"[]);
          data ~= elempref;
          data ~= ".byte\t1f - 0f\t/* size */";
          data ~= "0:";
          data ~= ".byte\t0x23\t/* DW_OP_plus_uconst */";
          data ~= ".uleb128\t0x8\t/* offset */";
          data ~= "1:";
        }
        sub ~= ptr;
      }
      return sect;
    }
  }
}

import ast.structfuns, ast.modules, ast.aliasing, ast.properties, ast.scopes, ast.assign;
Stuple!(IType, bool, Module, IType)[] cache;
bool[IType] isArrayStructType;
IType arrayAsStruct(IType base, bool rich) {
  auto mod = fastcast!(Module) (current_module());
  foreach (entry; cache)
    if (entry._0 == base /* hax */
     && entry._1 == rich
     && entry._2 is mod && mod.isValid) return entry._3;
  auto res = fastalloc!(Structure)(cast(string) null);
  res.sup = sysmod;
  if (rich)
    fastalloc!(RelMember)("capacity"[], Single!(SysInt), res);
  // TODO: fix when int promotion is supported
  // Structure.Member("length"[], Single!(SizeT)),
  fastalloc!(RelMember)("length"[], Single!(SysInt), res);
  fastalloc!(RelMember)("ptr"[], fastalloc!(Pointer)(base), res);
  res.name = "__array_as_struct__"~base.mangle()~(rich?"_rich":""[]);
  if (!mod || !sysmod || mod is sysmod || mod.name == "std.c.setjmp" /* hackaround */) {
    cache ~= stuple(base, rich, mod, fastcast!(IType) (res));
    return res;
  }
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(res);
  
  void mkFun(string name, IType ret, Tree delegate() dg) {
    auto fun = fastalloc!(RelFunction)(res);
    New(fun.type);
    fun.type.ret = ret;
    fun.name = name;
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    fun.sup = backup;
    namespace.set(fun);
    
    fun.fixup;
    fun.addStatement(fastcast!(Statement) (dg()));
    
    res.add(fun);
    fun.weak = true;
    mod.entries ~= fun;
  }
  cache ~= stuple(base, rich, mod, fastcast!(IType) (res));
  isArrayStructType[res] = true;
  mkFun("free"[], Single!(Void), delegate Tree() {
    if (rich) return iparse!(Statement, "array_free"[], "tree.stmt"[])
                  (`{ mem.free(void*:ptr); ptr = null; length = 0; capacity = 0; }`, namespace());
    else return iparse!(Statement, "array_free"[], "tree.stmt"[])
                  (`{ mem.free(void*:ptr); ptr = null; length = 0; }`, namespace());
  });
  if (!rich) {
    auto propbackup = propcfg().withTuple;
    propcfg().withTuple = true;
    scope(exit) propcfg().withTuple = propbackup;
    res.add(fastalloc!(ExprAlias)(
      iparse!(Expr, "array_dup"[], "tree.expr"[])
             (`(base*: dupv (ptr, length * size-of base))[0 .. length]`,
              res, "base"[], base),
      "dup"
    ));
  }
  if (base != Single!(Void) && base.size <= 16 /* max supported return size */) {
    mkFun("popEnd"[], base, delegate Tree() {
      auto len = fastcast!(LValue) (namespace().lookup("length"[]));
      auto p = fastcast!(Expr) (namespace().lookup("ptr"[]));
      return fastalloc!(ReturnStmt)(
        fastalloc!(StatementAndExpr)(
          fastalloc!(Assignment)(len, lookupOp("-"[], len, mkInt(1))),
          fastalloc!(DerefExpr)(lookupOp("+"[], p, len))
        )
      );
    });
  }
  
  return res;
}

T arrayToStruct(T)(T array) {
  auto avt = resolveType(array.valueType());
  auto
    ar = fastcast!(Array)~ avt,
    ea = fastcast!(ExtArray)~ avt;
  if (ar)
    return fastcast!(T)~ reinterpret_cast(arrayAsStruct(ar.elemType, false), array);
  if (ea)
    return fastcast!(T)~ reinterpret_cast(arrayAsStruct(ea.elemType, true),  array);
  logln(T.stringof, ": "[], array.valueType(), ": "[], array);
  fail;
  assert(false);
}

import ast.structure;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    // cur = forcedConvert(cur);
    if (text.accept("[]"[])) {
      return fastalloc!(Array)(cur);
    } else if (text.accept("[~]"[])) {
      return fastalloc!(ExtArray)(cur, false);
    } else if (text.accept("[auto ~]"[]) || text.accept("[auto~]"[]))
      return fastalloc!(ExtArray)(cur, true);
    else return null;
  };
}

import ast.pointer, ast.casting;

class ArrayLength_Base : Expr {
  Expr array;
  this(Expr a) { array = a; }
  private this() { }
  IType valueType() {
    return Single!(SysInt); // TODO: size_t when unsigned conversion works
  }
  void emitAsm(AsmFile af) {
    (new MemberAccess_Expr(arrayToStruct(array), "length"[])).emitAsm(af);
  }
  mixin defaultIterate!(array);
  mixin DefaultDup!();
}

class ArrayLength(T) : ArrayLength_Base, T {
  static if (is(T == MValue)) {
    alias LValue AT;
  } else {
    alias Expr AT;
  }
  this(AT at) {
    super(fastcast!(Expr) (at));
  }
  private this() { super(); }
  ArrayLength dup() { return fastalloc!(ArrayLength)(fastcast!(AT) (array.dup)); }
  override {
    IType valueType() {
      return Single!(SysInt); // TODO: size_t when unsigned conversion works
    }
    string toString() { return Format("length("[], array, ")"[]); }
    static if (is(T == MValue)) void emitAssignment(AsmFile af) {
      assert(false, "TODO"[]);
    }
  }
}

// construct array from two (three?) expressions
class ArrayMaker : Expr {
  Expr ptr, length;
  Expr cap;
  private this() { }
  this(Expr ptr, Expr length, Expr cap = null) {
    this.ptr = ptr; this.length = length; this.cap = cap;
  }
  mixin MyThis!("ptr, length, cap = null"[]);
  mixin DefaultDup!();
  mixin defaultIterate!(ptr, length, cap);
  IType elemType() {
    return (fastcast!(Pointer) (resolveType(ptr.valueType()))).target;
  }
  override string toString() { return Format("array(ptr="[], ptr, "[], length="[], length, cap?Format("[], cap="[], cap):""[], ")"[]); }
  IType cachedType;
  override IType valueType() {
    if (!cachedType) {
      if (cap) cachedType = fastalloc!(ExtArray)(elemType(), false);
      else cachedType = fastalloc!(Array)(elemType());
    }
    return cachedType;
  }
  import ast.vardecl, ast.assign;
  override void emitAsm(AsmFile af) {
    // TODO: stack direction/order
    ptr.emitAsm(af);
    length.emitAsm(af);
    if (cap)
      cap.emitAsm(af);
  }
}

import ast.variable, ast.vardecl;
class AllocStaticArray : Expr {
  Expr sa;
  StaticArray st;
  this(Expr sa) {
    this.sa = sa;
    st = fastcast!(StaticArray) (sa.valueType());
  }
  mixin defaultIterate!(sa);
  override {
    AllocStaticArray dup() { return fastalloc!(AllocStaticArray)(sa.dup); }
    IType valueType() { return fastalloc!(Array)(st.elemType); }
    void emitAsm(AsmFile af) {
      mkVar(af, valueType(), true, (Variable var) {
        sa.emitAsm(af);
        iparse!(Statement, "new_sa"[], "tree.stmt"[])
               (`var = new T[] size; `
               ,"var"[], var, "T"[], st.elemType, "size"[], mkInt(st.length)
               ).emitAsm(af);
        af.mmove4(qformat(4 + st.length, "(%esp)"[]), "%eax"[]);
        af.popStack("(%eax)"[], st.size);
      });
    }
  }
}

Expr staticToArray(Expr sa) {
  if (auto cv = fastcast!(CValue) (sa)) {
    return fastalloc!(ArrayMaker)(
      fastalloc!(CValueAsPointer)(cv),
      mkInt(fastcast!(StaticArray) (resolveType(sa.valueType())).length)
    );
  } else {
    return fastalloc!(AllocStaticArray)(sa);
  }
}

import ast.literals;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (!fastcast!(StaticArray)(ex.valueType()) || !fastcast!(CValue) (ex))
      return null;
    if (auto sa = fastcast!(StatementAnd) (ex))
      return mkStatementAndExpr(sa.first, staticToArray(sa.second));
    return staticToArray(ex);
  };
}

Expr getArrayLength(Expr ex) {
  if (auto sa = fastcast!(StaticArray) (resolveType(ex.valueType())))
    return mkInt(sa.length);
  if (auto lv = fastcast!(LValue) (ex)) return new ArrayLength!(MValue) (lv);
  else return new ArrayLength!(Expr) (ex);
}

Expr getArrayPtr(Expr ex) {
  if (auto sa = fastcast!(StaticArray) (resolveType(ex.valueType())))
    ex = staticToArray(ex);
  return mkMemberAccess(arrayToStruct!(Expr) (ex), "ptr"[]);
}

static this() {
  defineOp("length"[], delegate Expr(Expr ex) {
    ex = forcedConvert(ex);
    while (true) {
      if (auto ptr = fastcast!(Pointer) (ex.valueType()))
        ex = fastalloc!(DerefExpr)(ex);
      else break;
    }
    if (gotImplicitCast(ex, (IType it) { return fastcast!(Array) (it) || fastcast!(ExtArray) (it) || fastcast!(StaticArray) (it); })) {
      return getArrayLength(ex);
    } else return null;
  });
}

import ast.parse;
// separate because does clever allocation mojo .. eventually
Object gotArrayLength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    return fastcast!(Object) (lookupOp("length"[], ex));
  };
}
mixin DefaultParser!(gotArrayLength, "tree.rhs_partial.a_array_length"[], null, ".length"[]);

class ArrayExtender : Expr {
  Expr array, ext;
  IType baseType, cachedType;
  this(Expr a, Expr e) {
    array = a;
    ext = e;
    baseType = (fastcast!(Pointer) (getArrayPtr(array).valueType())).target;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(array, ext);
  override {
    IType valueType() { if (!cachedType) cachedType = fastalloc!(ExtArray)(baseType, false); return cachedType; }
    void emitAsm(AsmFile af) {
      array.emitAsm(af);
      ext.emitAsm(af);
    }
  }
}

static this() {
  implicits ~= delegate Expr(Expr ex, IType it) {
    if (!fastcast!(Array) (ex.valueType()) && !fastcast!(ExtArray) (ex.valueType())) return null;
    if (it && Single!(HintType!(Array)) != it && Single!(HintType!(ExtArray)) != it) return null;
    if (auto lv = fastcast!(LValue) (ex)) {
      if (auto sal = fastcast!(StatementAndLValue) (ex))
        return fastalloc!(StatementAndLValue)(sal.first, arrayToStruct!(LValue) (fastcast!(LValue) (sal.second)));
      return arrayToStruct!(LValue) (lv);
    } else {
      if (auto sae = fastcast!(StatementAndExpr) (ex))
        return fastalloc!(StatementAndExpr)(sae.first, arrayToStruct!(Expr) (sae.second));
      return arrayToStruct!(Expr) (ex);
    }
  };
  implicits ~= delegate Expr(Expr ex, IType it) {
    if (!fastcast!(Array) (ex.valueType())) return null;
    if (it && Single!(HintType!(Array)) != it && Single!(HintType!(ExtArray)) != it) return null;
    // if (!isTrivial(ex)) ex = lvize(ex);
    // equiv to extended with 0 cap
    return fastalloc!(ArrayExtender)(ex, mkInt(0));
  };
}

Expr arrayCast(Expr ex, IType it) {
  if (!gotImplicitCast(ex, (IType it) { return test(fastcast!(Array) (resolveType(it))); }))
    return null;
  auto ar1 = fastcast!(Array)~ resolveType(ex.valueType()), ar2 = fastcast!(Array)~ it;
  if (!ar1 || !ar2) return null;
  return iparse!(Expr, "array_cast_convert_call"[], "tree.expr"[])
                (`sys_array_cast!Res(from, sz1, sz2)`,
                 "Res"[], ar2, "from"[], ex,
                 "sz1"[], mkInt(ar1.elemType.size),
                 "sz2"[], mkInt(ar2.elemType.size));
}

import tools.base: todg;
import ast.opers, ast.namespace;
bool delegate(Expr, Expr, bool*) constantStringsCompare;
static this() {
  converts ~= &arrayCast /todg;
}

static this() {
  registerClass("ast.arrays"[], new ArrayLength!(MValue));
  registerClass("ast.arrays"[], new ArrayLength!(Expr));
}
