module casts;

import tools.log, tools.ctfe, tools.base: min;
import tools.base: Format, Stuple, stuple, Init, Repeat;
import alloc;

// list of class names to optimize
const string[] quicklist = [
  "ast.structure.Structure"[],
  "ast.structure.MemberAccess_LValue"[],
  "ast.types.Float"[],
  "ast.types.Void"[],
  "ast.pointer.Pointer"[],
  "ast.types.SysInt"[], 
  "ast.pointer.RefExpr"[],
  "ast.math.AsmIntBinopExpr"[],
  "ast.arrays.ArrayMaker"[],
  "ast.structure.StructLiteral"[],
  "ast.int_literal.IntExpr"[],
  "ast.propcall.MyPlaceholderExpr"[],
  "ast.casting.ReinterpretCast!(Expr).ReinterpretCast"[],
  "ast.propcall.FirstParamOverrideSpace"[],
  "ast.pointer.DerefExpr"[],
  "ast.casting.ReinterpretCast!(LValue).ReinterpretCast"[],
  "ast.variable.Variable"[],
  "ast.arrays.ExtArray"[],
  "ast.casting.IntLiteralAsShort"[],
  "ast.fun.FunCall"[],
  "ast.modules.Module"[],
  "ast.types.Byte"[],
  "ast.literals.FloatExpr"[],
  "ast.casting.ReinterpretCast!(MValue).ReinterpretCast"[],
  "ast.fun.Function"[],
  "ast.globvars.GlobVar"[],
  "ast.arrays.Array"[],
  "ast.tuples.Tuple"[],
  "ast.types.Char"[],
  "ast.math.IntAsFloat"[],
  "ast.casting.ShortToIntCast"[],
  "ast.tuples.RefTuple"[],
  "ast.structure.RelMember"[],
  "ast.math.IntAsLong"[],
  "ast.scopes.Scope"[],
  "ast.types.Long"[],
  "ast.types.Short"[],
  "ast.math.FloatAsDouble"[],
  "ast.types.Double"[],
  "ast.vector.Vector"[],
  "ast.structure.MemberAccess_Expr"[],
  "ast.funcall.DgCall"[],
  "ast.literals.CValueAsPointer"[],
  "ast.aliasing.ExprAlias"[],
  "ast.literal_string.StringExpr"[],
  "ast.tuples.LValueAsMValue"[],
  "ast.static_arrays.DataExpr"[],
  "ast.vector.VecOp"[],
  "ast.static_arrays.StaticArray"[],
  "ast.aliasing.TypeAlias"[],
  "ast.base.Filler"[],
  "ast.oop.ClassRef"[],
  "ast.oop.IntfRef"[],
  "ast.casting.ReinterpretCast!(CValue).ReinterpretCast"[],
  "ast.prefixfun.PrefixCall"[],
  "ast.base.PlaceholderToken"[],
  "ast.math.AsmFloatBinopExpr"[],
  "ast.vardecl.VarDecl"[],
  "ast.aliasing.LValueAlias"[],
  "ast.nestfun.NestedCall"[],
  "ast.parse.ExprStatement"[],
  "ast.iterator_ext.CrossIndexExpr"[],
  "ast.aggregate.AggrStatement"[],
  "ast.casting.DontCastMeExpr"[],
  "ast.casting.DontCastMeCValue"[],
  "ast.longmath.AsmLongBinopExpr"[],
  "ast.assign._Assignment!(LValue)._Assignment"[],
  "ast.base.Register!(\"ebp\").Register"[],
  "ast.dg.Delegate"[],
  "ast.structfuns.RelFunction"[],
  "ast.literals.DoubleExpr"[],
  "ast.vector.SSESwizzle"[],
  "ast.vector.AlignedVec4Literal"[],
  "ast.conditionals.Compare"[],
  "ast.vector.MultiplesExpr"[],
  "ast.vector.SSEIntToFloat"[],
  "ast.static_arrays.SALiteralExpr"[],
  "ast.namespace.MiniNamespace"[],
  "ast.conditionals.NegCond"[],
  "ast.base.LLVMValue"[],
  "ast.base.LLVMRef"[],
  "ast.fun.FunSymbol"[],
  "ast.base.PlaceholderTokenLV"[],
  "ast.structfuns.RelFunCall"[],
  "ast.conditionals.CondExpr"[],
  "ast.base.CallbackExpr"[],
  "ast.fun.FunctionPointer"[],
  "ast.base.WithTempExpr"[],
  "ast.conditionals.ExprWrap"[]
];

Stuple!(void*, int)[] idtable;

int xor, idmask;
const uint knuthMagic = 2654435761;

const cachesize = 1; // tested and best .. 0 is way slower, 2 is slightly slower.
void*[cachesize] pcache; int[cachesize] rescache;

void resetHash() { pcache[] = Init!(void*); }

uint internal_hash(void* p) {
  return cast(uint) (((cast(int) ((cast(size_t) p) >> 3)) ^ xor) * knuthMagic);
}

uint hash(void* p) {
  foreach_reverse (i, bogus; Repeat!(void, cachesize))
    if (pcache[i] == p) return rescache[i];
  uint res = internal_hash(p);
  foreach (i, bogus; Repeat!(void, cachesize - 1)) {
    pcache[i] = pcache[i+1];
    rescache[i] = rescache[i+1];
  }
  pcache[$-1] = p; rescache[$-1] = res;
  return res;
}

import tools.mersenne;

extern(C) void* memset(void*, int, size_t);

void initCastTable() {
  ClassInfo[] ci;
  foreach (entry; quicklist) {
    auto cl = ClassInfo.find(entry);
    if (!cl) {
      logln("No such class: "[], entry);
      continue;
    }
    ci ~= cl;
  }
  int bestXOR, bestXORSize = int.max, bestMask;
  auto rng = fastalloc!(Mersenne)(23);
  auto backing_pretable = new bool[1024];
  bool[] pretable;
  void resize_pretable(int to) {
    while (to >= backing_pretable.length) backing_pretable = new typeof(pretable[0])[backing_pretable.length * 2];
    pretable = backing_pretable[0..to];
    memset(pretable.ptr, false, pretable.length);
  }
  for (int i = 0; i < 512; ++i) {
    // lol
    xor = rng();
    // auto cursize = quicklist.length;
    int cursize = 2, curmask = 1;
    outer:
    resize_pretable(cursize);
    resetHash();
    foreach (int id, entry; ci) {
      auto pos = hash(cast(void*) entry) % pretable.length;
      if (pretable[pos]) {
        // cursize ++;
        cursize *= 2; curmask = (curmask << 1) | 1;
        if (cursize >= bestXORSize) break;
        goto outer;
      }
      pretable[pos] = true;
    }
    if (cursize < bestXORSize) {
      bestXOR = xor;
      bestXORSize = cursize;
      bestMask = curmask;
    }
  }
  xor = bestXOR;
  idtable.length = bestXORSize;
  idmask = bestMask;
  
  memset(idtable.ptr, 0, idtable.length * typeof(idtable[0]).sizeof);
  resetHash();
  foreach (int i, entry; ci) {
    idtable[hash(cast(void*) entry) & idmask] = stuple(cast(void*) entry, i);
  }
}

const getIdCacheSize = 1; // more is sliightly slower, less is way slower
Stuple!(void*, int)[getIdCacheSize] getIdCache;
int getIdLoopPtr;
// version(Windows) { } else pragma(set_attribute, getId, optimize("-O3"));
int getId(ClassInfo ci) {
  auto cp = cast(void*) ci;
  static if (getIdCacheSize) foreach (i, bogus; Repeat!(void, getIdCacheSize)) {
    int idx = (i + getIdLoopPtr + 1) % getIdCacheSize;
    if (getIdCache[idx]._0 == cp)
      return getIdCache[idx]._1;
  }
  auto entry = idtable.ptr[hash(cp) & idmask];
  int res = (entry._0 == cp)?entry._1:-1;
  static if (getIdCacheSize) {
    auto p = &getIdCache[getIdLoopPtr];
    p._0 = cp; p._1 = res; //  = stuple(cp, res);
    static if (getIdCacheSize > 1) {
      getIdLoopPtr --;
      if (getIdLoopPtr < 0) getIdLoopPtr += getIdCacheSize;
    }
  }
  return res;
}

extern(C) void fastcast_marker() { }

template fastcast_direct(T) {
  T fastcast_direct(U)(U u) {
    Object obj = void;
    // stolen from fastcast
    static if (!is(U: Object)) { // interface
      auto ptr = **cast(Interface***) u;
      void* vp = cast(void*) u - ptr.offset;
      obj = *cast(Object*) &vp;
    } else {
      void* vp = cast(void*) u;
      obj = *cast(Object*) &vp;
    }
    
    if (obj.classinfo !is T.classinfo) return null;
    return *cast(T*) &obj; // prevent a redundant D cast
  }
}

template staticCastCache(T, U) {
  int cache = -1;
}
struct _fastcast(T) {
  const ptrdiff_t INVALID = 0xffff; // magic numbah
  static ptrdiff_t[quicklist.length] offsets;
  T opCall(U)(U u) {
    if (!u) return null;
    static assert (!is(U == void*));
    
    Object obj;
    
    const string fillObj = `
    {static if (!is(U: Object)) { // interface
      auto ptr = **cast(Interface***) u;
      void* vp = cast(void*) u - ptr.offset;
      obj = *cast(Object*) &vp;
    } else {
      void* vp = cast(void*) u;
      obj = *cast(Object*) &vp; // prevent a redundant D cast
    }}`;
    static if (is(typeof(T.isFinal)) && T.isFinal) {
      // deterministic
      mixin(fillObj);
      if (obj.classinfo !is T.classinfo) return null;
      return *cast(T*)&obj;
    }
    // logln("Cast "[], (cast(Object) u).classinfo.name);
    // this doesn't do much but I'm leaving it in so you don't think I didn't think of it.
    // ACTUALLY NO BAD BAD NO
    // THERE ARE SITUATIONS (IN D) WHERE THIS **DOES NOT** HOLD
    // WE *ALWAYS* HAVE TO USE THE ACTUAL CLASS OF THE OBJECT AS THE HASH KEY.
    // I don't understand the situation yet so I'm not quite certain if D fucks up horribly
    // or if my understanding of interface liskov semantics is just flawed. I
    // hope the latter because this is BIG.
    static if (false && is(U: T) && !is(T: Object)) {{ // liskov says we can do this deterministically
      // direct parent of interface cast
      int hint = staticCastCache!(T, U).cache;
      if (hint == -1) {
        // cast(Object) necessary to work around D bug
        auto dest = cast(T) cast(Object) u;
        hint = cast(void*) dest - cast(void*) u;
        staticCastCache!(T, U).cache = hint;
      } else {
        auto dest = cast(T) cast(Object) u;
        auto newhint = cast(void*) dest - cast(void*) u;
        if (hint != newhint) {
          logln("wat ", hint, " - ", newhint, " ", T.stringof, " ", U.stringof);
          asm { int 3; }
        }
      }
      auto temp = cast(void*) u + hint;
      return *cast(T*) &temp;
    }}
    if (!idtable.length)
      return cast(T) u; // not initialized yet (called from a static constructor?)
    fastcast_marker();
    if (!obj) mixin(fillObj);
    static if (is(T == Object)) return obj;
    // implicit downcast - make sure we want a class!
    static if (is(U: T) && is(T: Object)) { return *cast(T*) &obj; }
    auto info = obj.classinfo;
    auto id = getId(info);
    if (id == -1) {
      // logln("Boring cast: "[], info.name);
      return cast(T) cast(Object) u;
    }
    auto hint = offsets[id];
    if (hint == INVALID) return null;
    if (!hint) {
      // cast(Object) necessary to work around D bug
      auto res = cast(T) cast(Object) obj;
      if (res)
        offsets[id] = (cast(void*) res - cast(void*) obj) + 1;
      else
        offsets[id] = INVALID;
      return res;
    }
    return cast(T) (cast(void*) obj + (hint - 1));
  }
  alias opCall opCat;
}

template fastcast(T) {
  _fastcast!(T) fastcast;
}
