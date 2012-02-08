module ast.arrays;

import ast.base, ast.types, ast.static_arrays, ast.returns, tools.base: This, This_fn, rmSpace;

// ptr, length
final class Array : Type {
  IType elemType;
  this() { }
  this(IType et) { elemType = forcedConvert(et); }
  override {
    // bool isComplete() { return elemType.isComplete; }
    bool isComplete() { return true; /* size not determined by element size! */ }
    int size() {
      return nativePtrSize + nativeIntSize;
    }
    string mangle() {
      return "array_of_"~elemType.mangle();
    }
    string toString() { return Format(elemType, "[]"); }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      ty = resolveType(ty);
      return (fastcast!(Array) (ty)).elemType == elemType;
    }
    bool isPointerLess() { return false; }
  }
}

// ptr, length, capacity
class ExtArray : Type {
  IType elemType;
  bool freeOnResize;
  this() { }
  this(IType et, bool fOR) { elemType = forcedConvert(et); freeOnResize = fOR; }
  override {
    int size() {
      return nativePtrSize + nativeIntSize * 2;
    }
    string mangle() {
      return "rich_array_of_"~elemType.mangle();
    }
    int opEquals(IType ty) {
      if (!super.opEquals(ty)) return false;
      ty = resolveType(ty);
      auto ea = fastcast!(ExtArray) (ty);
      return ea.elemType == elemType && ea.freeOnResize == freeOnResize;
    }
    string toString() {
      return Format(elemType, "[", freeOnResize?"auto ":"", "~]");
    }
  }
}

import ast.structfuns, ast.modules, ast.aliasing, ast.properties, ast.scopes;
Stuple!(IType, bool, Module, IType)[] cache;
bool[IType] isArrayStructType;
IType arrayAsStruct(IType base, bool rich) {
  auto mod = fastcast!(Module) (current_module());
  foreach (entry; cache)
    if (entry._0 == base /* hax */
     && entry._1 == rich
     && entry._2 is mod && mod.isValid) return entry._3;
  auto res = new Structure(null);
  res.sup = sysmod;
  if (rich)
    new RelMember("capacity", Single!(SysInt), res);
  // TODO: fix when int promotion is supported
  // Structure.Member("length", Single!(SizeT)),
  new RelMember("length", Single!(SysInt), res);
  new RelMember("ptr", new Pointer(base), res);
  res.name = "__array_as_struct__"~base.mangle()~(rich?"_rich":"");
  if (!mod || !sysmod || mod is sysmod || mod.name == "std.c.setjmp" /* hackaround */) return res;
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(res);
  
  void mkFun(string name, Tree delegate() dg) {
    auto fun = new RelFunction(res);
    New(fun.type);
    fun.type.ret = Single!(Void);
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
  mkFun("free", delegate Tree() {
    if (rich) return iparse!(Statement, "array_free", "tree.stmt")
                  (`{ mem.free(void*:ptr); ptr = null; length = 0; capacity = 0; }`, namespace());
    else return iparse!(Statement, "array_free", "tree.stmt")
                  (`{ mem.free(void*:ptr); ptr = null; length = 0; }`, namespace());
  });
  if (!rich) {
    auto propbackup = propcfg().withTuple;
    propcfg().withTuple = true;
    scope(exit) propcfg().withTuple = propbackup;
    res.add(new ExprAlias(
      iparse!(Expr, "array_dup", "tree.expr")
             (`(base*: dupv (ptr, length * size-of base))[0 .. length]`,
              res, "base", base),
      "dup"
    ));
  }
  if (base != Single!(Void) && base.size <= 16 /* max supported return size */) {
    mkFun("popEnd", delegate Tree() {
      namespace().get!(RelFunction).type.ret = base;
      return new ReturnStmt(
        new StatementAndExpr(
          iparse!(Statement, "array_setpop", "tree.stmt")
                (`length --;`, namespace()),
          iparse!(Expr, "array_getpop", "tree.expr")
                (`*(ptr + length)`, namespace())
        )
      );
    });
  }
  
  cache ~= stuple(base, rich, mod, fastcast!(IType) (res));
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
  fail;
  assert(false);
}

import ast.structure;
static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    // cur = forcedConvert(cur);
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

class ArrayLength_Base : Expr {
  Expr array;
  this(Expr a) { array = a; }
  private this() { }
  IType valueType() {
    return Single!(SysInt); // TODO: size_t when unsigned conversion works
  }
  void emitAsm(AsmFile af) {
    (new MemberAccess_Expr(arrayToStruct(array), "length")).emitAsm(af);
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
  ArrayLength dup() { return new ArrayLength(fastcast!(AT) (array)); }
  override {
    IType valueType() {
      return Single!(SysInt); // TODO: size_t when unsigned conversion works
    }
    string toString() { return Format("length(", array, ")"); }
    static if (is(T == MValue)) void emitAssignment(AsmFile af) {
      assert(false, "TODO");
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
  mixin MyThis!("ptr, length, cap = null");
  mixin DefaultDup!();
  mixin defaultIterate!(ptr, length, cap);
  IType elemType() {
    return (fastcast!(Pointer) (resolveType(ptr.valueType()))).target;
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
               (`var = new T[] size; `
               ,"var", var, "T", st.elemType, "size", mkInt(st.length)
               ).emitAsm(af);
        af.mmove4(qformat(4 + st.length, "(%esp)"), "%eax");
        af.popStack("(%eax)", st.size);
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
  if (auto sa = fastcast!(StaticArray) (resolveType(ex.valueType())))
    return mkInt(sa.length);
  if (auto lv = fastcast!(LValue) (ex)) return new ArrayLength!(MValue) (lv);
  else return new ArrayLength!(Expr) (ex);
}

Expr getArrayPtr(Expr ex) {
  return mkMemberAccess(arrayToStruct!(Expr) (ex), "ptr");
}

static this() {
  defineOp("length", delegate Expr(Expr ex) {
    while (true) {
      if (auto ptr = fastcast!(Pointer) (ex.valueType()))
        ex = new DerefExpr(ex);
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
    return fastcast!(Object) (lookupOp("length", ex));
  };
}
mixin DefaultParser!(gotArrayLength, "tree.rhs_partial.a_array_length", null, ".length");

class ArrayExtender : Expr {
  Expr array, ext;
  IType baseType;
  this(Expr a, Expr e) {
    array = a;
    ext = e;
    baseType = (fastcast!(Pointer) (getArrayPtr(array).valueType())).target;
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(array, ext);
  override {
    IType valueType() { return new ExtArray(baseType, false); }
    void emitAsm(AsmFile af) {
      array.emitAsm(af);
      ext.emitAsm(af);
    }
  }
}

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
    // if (!isTrivial(ex)) ex = lvize(ex);
    // equiv to extended with 0 cap
    return new ArrayExtender(ex, mkInt(0));
  };
}

Expr arrayCast(Expr ex, IType it) {
  if (!gotImplicitCast(ex, (IType it) { return test(fastcast!(Array) (resolveType(it))); }))
    return null;
  auto ar1 = fastcast!(Array)~ resolveType(ex.valueType()), ar2 = fastcast!(Array)~ it;
  if (!ar1 || !ar2) return null;
  return iparse!(Expr, "array_cast_convert_call", "tree.expr")
                (`sys_array_cast!Res(from, sz1, sz2)`,
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
    auto res = iparse!(Expr, "array_eq", "tree.expr.eval.cond")
                  (`eval (ex1.length == ex2.length && memcmp(void*:ex1.ptr, void*:ex2.ptr, ex1.length * (size-of type-of ex1[0])) == 0)`,
                   "ex1", lvize(ex1), "ex2", lvize(ex2));
    assert(!!res);
    return res;
  });
}

static this() {
  registerClass("ast.arrays", new ArrayLength!(MValue));
  registerClass("ast.arrays", new ArrayLength!(Expr));
}
