module ast.arrays;

import ast.base, ast.types, ast.static_arrays, tools.base: This, This_fn, rmSpace;

// ptr, length
class Array : Type {
  IType elemType;
  this() { }
  this(IType et) { elemType = et; }
  override {
    int size() {
      return nativePtrSize + nativeIntSize;
    }
    string mangle() {
      return "array_of_"~elemType.mangle();
    }
    string toString() { return Format(elemType, "[]"); }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      while (true) {
        if (auto tp = fastcast!(TypeProxy)~ ty) ty = tp.actualType();
        else break;
      }
      return (fastcast!(Array)~ ty).elemType == elemType;
    }
  }
}

// ptr, length, capacity
class ExtArray : Type {
  IType elemType;
  bool freeOnResize;
  this() { }
  this(IType et, bool fOR) { elemType = et; freeOnResize = fOR; }
  override {
    int size() {
      return nativePtrSize + nativeIntSize * 2;
    }
    string mangle() {
      return "rich_array_of_"~elemType.mangle();
    }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      while (true) {
        if (auto tp = fastcast!(TypeProxy)~ ty) ty = tp.actualType();
        else break;
      }
      auto ea = fastcast!(ExtArray)~ ty;
      return ea.elemType == elemType && ea.freeOnResize == freeOnResize;
    }
    string toString() {
      return Format(elemType, "[", freeOnResize?"auto ":"", "~]");
    }
  }
}

import ast.structfuns, ast.modules;
Stuple!(IType, bool, IType)[] cache;
bool[IType] isArrayStructType;
IType arrayAsStruct(IType base, bool rich) {
  foreach (entry; cache)
    if (entry._0 == base && entry._1 == rich) return entry._2;
  auto res = new Structure(null);
  if (rich)
    new RelMember("capacity", Single!(SysInt), res);
  // TODO: fix when int promotion is supported
  // Structure.Member("length", Single!(SizeT)),
  new RelMember("length", Single!(SysInt), res);
  new RelMember("ptr", new Pointer(base), res);
  res.name = "__array_as_struct__"~base.mangle()~(rich?"_rich":"");
  if (!extras || !sysmod || !sysmod.parsingDone) return res;
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(res);
  
  void mkFun(string name, Tree delegate(RelFunction) dg) {
    auto fun = new RelFunction(res);
    New(fun.type);
    fun.type.ret = Single!(Void);
    fun.name = name;
    fun.fixup;
    auto backup2 = namespace();
    scope(exit) namespace.set(backup2);
    namespace.set(fun);
    fun.tree = dg(fun);
    res.add(fun);
    addExtra(fun);
  }
  mkFun("free", delegate Tree(RelFunction rf) {
    if (rich) return iparse!(Statement, "array_free", "tree.stmt")
                  (`{ mem.free(void*:ptr); ptr = null; length = 0; capacity = 0; }`, rf);
    else return iparse!(Statement, "array_free", "tree.stmt")
                  (`{ mem.free(void*:ptr); ptr = null; length = 0; }`, rf);
  });
  mkFun("popEnd", delegate Tree(RelFunction rf) {
    rf.type.ret = base;
    return new StatementAndExpr(
      iparse!(Statement, "array_setpop", "tree.stmt")
             (`length --;`, rf),
      iparse!(Expr, "array_getpop", "tree.expr")
             (`*(ptr + length)`, rf)
    );
  });
  
  cache ~= stuple(base, rich, fastcast!(IType)~ res);
  isArrayStructType[res] = true;
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
  logln(T.stringof, ": ", array.valueType(), ": ", array);
  asm { int 3; }
  assert(false);
}

import ast.structure;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    if (text.accept("[]")) {
      return new Array(cur);
    } else if (text.accept("[~]")) {
      return new ExtArray(cur, false);
    } else if (text.accept("[auto ~]") || text.accept("[auto~]"))
      return new ExtArray(cur, true);
    else return null;
  };
}

import ast.pointer, ast.casting;
class ArrayLength(T) : T {
  static if (is(T == MValue)) {
    alias LValue AT;
  } else {
    alias Expr AT;
  }
  AT array;
  this(AT at) {
    array = at;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(array);
  override {
    string toString() { return Format("length(", array, ")"); }
    IType valueType() {
      return Single!(SysInt); // TODO: size_t when unsigned conversion works
    }
    void emitAsm(AsmFile af) {
      (new MemberAccess_Expr(arrayToStruct(array), "length")).emitAsm(af);
    }
    static if (is(T == MValue)) void emitAssignment(AsmFile af) {
      assert(false, "TODO");
    }
  }
}

// construct array from two (three?) expressions
class ArrayMaker : Expr {
  Expr ptr, length;
  Expr cap;
  mixin MyThis!("ptr, length, cap = null");
  mixin DefaultDup!();
  mixin defaultIterate!(ptr, length, cap);
  IType elemType() {
    return (fastcast!(Pointer)~ ptr.valueType()).target;
  }
  override string toString() { return Format("array(ptr=", ptr, ", length=", length, cap?Format(", cap=", cap):"", ")"); }
  IType cachedType;
  override IType valueType() {
    if (!cachedType) {
      if (cap) cachedType = new ExtArray(elemType(), false);
      else cachedType = new Array(elemType());
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
    AllocStaticArray dup() { return new AllocStaticArray(sa.dup); }
    IType valueType() { return new Array(st.elemType); }
    void emitAsm(AsmFile af) {
      mkVar(af, valueType(), true, (Variable var) {
        sa.emitAsm(af);
        iparse!(Statement, "new_sa", "tree.stmt")
               (`var = new T[size]; `
               ,"var", var, "T", st.elemType, "size", mkInt(st.length)
               ).emitAsm(af);
        af.mmove4(qformat(4 + st.length, "(%esp)"), "%eax");
        af.popStack("(%eax)", st);
      });
    }
  }
}

Expr staticToArray(Expr sa) {
  if (auto cv = fastcast!(CValue) (sa)) {
    return new ArrayMaker(
      new CValueAsPointer(cv),
      mkInt((fastcast!(StaticArray)~ sa.valueType()).length)
    );
  } else {
    return new AllocStaticArray(sa);
  }
}

import ast.literals;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (!fastcast!(StaticArray)(ex.valueType()) || !fastcast!(CValue) (ex))
      return null;
    return staticToArray(ex);
  };
}

Expr getArrayLength(Expr ex) {
  if (auto sa = fastcast!(StaticArray)~ resolveType(ex.valueType()))
    return mkInt(sa.length);
  if (auto lv = fastcast!(LValue)~ ex) return new ArrayLength!(MValue) (lv);
  else return new ArrayLength!(Expr) (ex);
}

Expr getArrayPtr(Expr ex) {
  return mkMemberAccess(arrayToStruct!(Expr) (ex), "ptr");
}

import ast.parse;
// separate because does clever allocation mojo .. eventually
Object gotArrayLength(ref string text, ParseCb cont, ParseCb rest) {
  return lhs_partial.using = delegate Object(Expr ex) {
    if (fastcast!(Array)~ ex.valueType() || fastcast!(ExtArray)~ ex.valueType()) {
      return fastcast!(Object)~ getArrayLength(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotArrayLength, "tree.rhs_partial.array_length", null, ".length");

static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (!fastcast!(Array) (ex.valueType()) && !fastcast!(ExtArray) (ex.valueType())) return null;
    if (auto lv = fastcast!(LValue)~ ex)
      return arrayToStruct!(LValue) (lv);
    else
      return arrayToStruct!(Expr) (ex);
  };
  implicits ~= delegate Expr(Expr ex) {
    if (!fastcast!(Array) (ex.valueType())) return null;
    // equiv to extended with 0 cap
    return new ArrayMaker(getArrayPtr(ex), getArrayLength(ex), mkInt(0));
  };
}

Expr arrayCast(Expr ex, IType it) {
  auto ar1 = fastcast!(Array)~ resolveType(ex.valueType()), ar2 = fastcast!(Array)~ it;
  if (!ar1 || !ar2) return null;
  return iparse!(Expr, "array_cast_convert_call", "tree.expr")
                (`sys_array_cast!Res(from.ptr, from.length, sz1, sz2)`,
                 "Res", ar2, "from", ex,
                 "sz1", mkInt(ar1.elemType.size),
                 "sz2", mkInt(ar2.elemType.size));
}

import tools.base: todg;
import ast.opers, ast.namespace;
static this() {
  converts ~= &arrayCast /todg;
  defineOp("==", delegate Expr(Expr ex1, Expr ex2) {
    bool isArray(IType it) { return !!fastcast!(Array) (it); }
    if (!gotImplicitCast(ex1, &isArray) || !gotImplicitCast(ex2, &isArray))
      return null;
    auto res = iparse!(Expr, "array_eq", "tree.expr")
                  (`eval (ex1.length == ex2.length && memcmp(void*:ex1.ptr, void*:ex2.ptr, ex1.length * (size-of type-of ex1[0])) == 0)`,
                   "ex1", ex1, "ex2", ex2);
    assert(!!res);
    return res;
  });
}
