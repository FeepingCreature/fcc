module casts;

import tools.log, tools.ctfe, tools.compat: min;
import tools.base: Format, Stuple, stuple, Init, Repeat;

// list of class names to optimize
const string[] quicklist = [
  "ast.structure.Structure",
  "ast.structure.MemberAccess_LValue",
  "ast.types.Float",
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
  "ast.oop.IntfRef"
  "ast.casting.ReinterpretCast!(CValue).ReinterpretCast"
];

Stuple!(void*, int)[] idtable;

int xor;
const uint knuthMagic = 2654435761;

const cachesize = 1; // tested and best
void*[cachesize] pcache; int[cachesize] rescache;

void resetHash() { pcache[] = Init!(void*); }

// int is okay here; we don't expect variation in the upper bits
int hash(void* p) {
  foreach_reverse (i, bogus; Repeat!(void, cachesize))
    if (pcache[i] == p) return rescache[i];
  int res = cast(uint) (((cast(int) cast(size_t) p >> 3) ^ xor) * knuthMagic) % idtable.length;
  foreach (i, bogus; Repeat!(void, cachesize - 1)) {
    pcache[i] = pcache[i+1];
    rescache[i] = rescache[i+1];
  }
  pcache[$-1] = p; rescache[$-1] = res;
  return res;
}

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
  int bestXOR, bestXORSize = int.max;
  for (int i = 0; i < 512; ++i) {
    // lol
    xor = rand();
    auto cursize = quicklist.length;
    outer:
    idtable.length = cursize;
    idtable[] = Init!(Stuple!(void*, int));
    resetHash();
    foreach (int id, entry; ci) {
      auto pos = hash(cast(void*) entry);
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
  idtable[] = Init!(Stuple!(void*, int));
  resetHash();
  foreach (int i, entry; ci) {
    auto pos = hash(cast(void*) entry);
    idtable[pos] = stuple(cast(void*) entry, i);
  }
}

int getId(ClassInfo ci) {
  auto cp = cast(void*) ci;
  auto entry = idtable[hash(cp)];
  if (entry._0 == cp) return entry._1;
  return -1;
}

struct _fastcast(T) {
  const ptrdiff_t INVALID = 0xffff; // magic numbah
  static ptrdiff_t[quicklist.length] offsets;
  T opCall(U)(U u) {
    if (!u) return null;
    static assert (!is(U == void*));

    // logln("Cast ", (cast(Object) u).classinfo.name);
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
