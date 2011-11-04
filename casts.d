module casts;

import tools.log, tools.ctfe, tools.compat: min;
import tools.base: Format, Stuple, stuple, Init, Repeat;

// list of class names to optimize
const string[] quicklist = [
  "ast.structure.Structure",
  "ast.structure.MemberAccess_LValue",
  "ast.types.Float",
  "ast.types.Void",
  "ast.pointer.Pointer",
  "ast.types.SysInt", 
  "ast.pointer.RefExpr",
  "ast.math.AsmIntBinopExpr",
  "ast.arrays.ArrayMaker",
  "ast.structure.StructLiteral",
  "ast.int_literal.IntExpr",
  "ast.propcall.MyPlaceholderExpr",
  "ast.casting.ReinterpretCast!(Expr).ReinterpretCast",
  "ast.propcall.FirstParamOverrideSpace",
  "ast.pointer.DerefExpr",
  "ast.casting.ReinterpretCast!(LValue).ReinterpretCast",
  "ast.variable.Variable",
  "ast.arrays.ExtArray",
  "ast.math.IntLiteralAsShort",
  "ast.fun.FunCall",
  "ast.modules.Module",
  "ast.types.Byte",
  "ast.literals.FloatExpr",
  "ast.casting.ReinterpretCast!(MValue).ReinterpretCast",
  "ast.fun.Function",
  "ast.globvars.GlobVar",
  "ast.arrays.Array",
  "ast.tuples.Tuple",
  "ast.types.Char",
  "ast.math.IntAsFloat",
  "ast.casting.ShortToIntCast",
  "ast.tuples.RefTuple",
  "ast.structure.RelMember",
  "ast.math.IntAsLong",
  "ast.scopes.Scope",
  "ast.types.Long",
  "ast.types.Short",
  "ast.math.FloatAsDouble",
  "ast.types.Double",
  "ast.vector.Vector",
  "ast.structure.MemberAccess_Expr",
  "ast.funcall.DgCall",
  "ast.literals.CValueAsPointer",
  "ast.aliasing.ExprAlias",
  "ast.literal_string.StringExpr",
  "ast.tuples.LValueAsMValue",
  "ast.static_arrays.DataExpr",
  "ast.vector.VecOp",
  "ast.static_arrays.StaticArray",
  "ast.aliasing.TypeAlias",
  "ast.base.Filler",
  "ast.oop.ClassRef",
  "ast.oop.IntfRef",
  "ast.casting.ReinterpretCast!(CValue).ReinterpretCast",
  "ast.mode.PrefixCall",
  "ast.arrays.ArrayLength!(MValue).ArrayLength",
  "ast.base.PlaceholderToken",
  "ast.math.AsmFloatBinopExpr",
  "ast.vardecl.VarDecl",
  "ast.aliasing.LValueAlias",
  "ast.arrays.ArrayLength!(Expr).ArrayLength",
  "ast.nestfun.NestedCall",
  "ast.parse.ExprStatement",
  "ast.iterator_ext.CrossIndexExpr",
  "ast.context.Context",
  "ast.aggregate.AggrStatement",
  "ast.casting.DontCastMeExpr",
  "ast.casting.DontCastMeCValue",
  "ast.longmath.AsmLongBinopExpr",
  "ast.assign._Assignment!(LValue)._Assignment",
  "ast.base.Register!(\"ebp\").Register",
  "ast.dg.Delegate",
  "ast.structfuns.RelFunction",
  "ast.literals.DoubleExpr",
  "ast.vector.SSESwizzle",
  "ast.vector.AlignedVec4Literal",
  "ast.conditionals.Compare",
  "ast.vector.MultiplesExpr",
  "ast.vector.SSEIntToFloat",
  "ast.static_arrays.SALiteralExpr",
  "ast.namespace.MiniNamespace"
];

Stuple!(void*, int)[] idtable;
const predIdtableLength = 161; // predicted idtable length - slight hash speed up

int xor;
const uint knuthMagic = 2654435761;

const cachesize = 1; // tested and best .. 0 is way slower, 2 is slightly slower.
void*[cachesize] pcache; int[cachesize] rescache;

void resetHash() { pcache[] = Init!(void*); }

uint internal_hash(void* p) {
  return cast(uint) (((cast(int) ((cast(size_t) p) >> 3)) ^ xor) * knuthMagic);
}

// int is okay here; we don't expect variation in the upper bits
int hash_dyn(void* p) {
  foreach_reverse (i, bogus; Repeat!(void, cachesize))
    if (pcache[i] == p) return rescache[i];
  int res = internal_hash(p) % idtable.length;
  foreach (i, bogus; Repeat!(void, cachesize - 1)) {
    pcache[i] = pcache[i+1];
    rescache[i] = rescache[i+1];
  }
  pcache[$-1] = p; rescache[$-1] = res;
  return res;
}

// copypasted to make profiling slightly easier. only difference should be idtable.length
// TODO: comment in for release builds
/*int hash_stat(void* p) {
  foreach_reverse (i, bogus; Repeat!(void, cachesize))
    if (pcache[i] == p) return rescache[i];
  int res = cast(uint) (((cast(int) cast(size_t) p >> 3) ^ xor) * knuthMagic) % predIdtableLength;
  foreach (i, bogus; Repeat!(void, cachesize - 1)) {
    pcache[i] = pcache[i+1];
    rescache[i] = rescache[i+1];
  }
  pcache[$-1] = p; rescache[$-1] = res;
  return res;
}*/
alias hash_dyn hash_stat;

import tools.mersenne;

void initCastTable() {
  ClassInfo[] ci;
  foreach (entry; quicklist) {
    auto cl = ClassInfo.find(entry);
    if (!cl) {
      logln("No such class: ", entry);
      continue;
    }
    ci ~= cl;
  }
  auto precache = new uint[ci.length];
  foreach (int id, entry; ci)
    precache[id] = internal_hash(cast(void*) entry);
  
  int bestXOR, bestXORSize = int.max;
  auto rng = new Mersenne(23);
  for (int i = 0; i < 512; ++i) {
    // lol
    xor = rng();
    auto cursize = quicklist.length;
    outer:
    idtable.length = cursize;
    idtable[] = Init!(Stuple!(void*, int));
    resetHash();
    foreach (int id, entry; ci) {
      // auto pos = hash_dyn(cast(void*) entry);
      auto pos = precache[id] % idtable.length;
      if (idtable[pos]._0) {
        cursize ++;
        if (cursize >= bestXORSize) break;
        goto outer;
      }
      idtable[pos]._0 = cast(void*) entry;
    }
    if (cursize < bestXORSize) {
      bestXORSize = cursize;
      bestXOR = xor;
    }
  }
  xor = bestXOR;
  idtable.length = bestXORSize;
  /*if (idtable.length != predIdtableLength) {
    logln("please update pred const to ", idtable.length);
    asm { int 3; }
  }*/
  idtable[] = Init!(Stuple!(void*, int));
  resetHash();
  foreach (int i, entry; ci) {
    auto pos = hash_stat(cast(void*) entry);
    idtable[pos] = stuple(cast(void*) entry, i);
  }
}

int getId(ClassInfo ci) {
  auto cp = cast(void*) ci;
  // we know it's a valid index
  auto entry = idtable.ptr[hash_stat(cp)];
  if (entry._0 == cp) return entry._1;
  return -1;
}

extern(C) void fastcast_marker() { }

struct _fastcast(T) {
  const ptrdiff_t INVALID = 0xffff; // magic numbah
  static ptrdiff_t[quicklist.length] offsets;
  template staticCache(U) {
    int cache = -1;
  }
  T opCall(U)(U u) {
    if (!u) return null;
    static assert (!is(U == void*));
    
    // logln("Cast ", (cast(Object) u).classinfo.name);
    // this doesn't do much but I'm leaving it in so you don't think I didn't think of it.
    static if (is(U: T) && !is(T: Object)) {{ // liskov says we can do this deterministically
      // direct parent of interface cast
      int hint = staticCache!(U).cache;
      if (hint == -1) {
        auto dest = cast(T) u;
        hint = cast(void*) dest - cast(void*) u;
        staticCache!(U).cache = hint;
      }
      auto temp = cast(void*) u + hint;
      return *cast(T*) &temp;
    }}
    if (!idtable.length)
      return cast(T) u; // not initialized yet (called from a static constructor?)
    fastcast_marker();
    Object obj;
    static if (!is(U: Object)) { // interface
      auto ptr = **cast(Interface***) u;
      void* vp = *cast(void**) &u - ptr.offset;
      obj = *cast(Object*) &vp;
    } else {
      void* vp = *cast(void**) &u;
      obj = *cast(Object*) &vp; // prevent a redundant D cast
    }
    static if (is(T == Object)) return obj;
    // implicit downcast - make sure we want a class!
    static if (is(U: T) && is(T: Object)) { return *cast(T*) &obj; }
    auto id = getId(obj.classinfo);
    if (id == -1) {
      // logln("Boring cast: ", obj.classinfo.name);
      return cast(T) u;
    }
    auto hint = offsets[id];
    if (hint == INVALID) return null;
    if (!hint) {
      auto res = cast(T) obj;
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
