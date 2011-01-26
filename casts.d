module casts;

import tools.log, tools.ctfe, tools.compat: min;
import tools.base: Format, Stuple, Init;

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
  "ast.aliasing.TypeAlias"
];

Stuple!(void*, int)[] idtable;

struct PrimeGenerator {
  int[] cache;
  int last;
  void reset() { last = 0; }
  int gen() {
    if (!last) { last = 1; return last; }
    auto cur = last;
    while (true) {
      cur ++;
      foreach (entry; cache) {
        if (cur % entry == 0) { continue; }
        if (entry * entry > cur) { break; }
      }
      break;
    }
    if (!cache.length || cache[$-1] < cur)
      cache ~= cur;
    return cur;
  }
}

void initTable() {
  ClassInfo[] ci;
  foreach (entry; quicklist) ci ~= ClassInfo.find(entry);
  auto cursize = quicklist.length * 4;
  PrimeGenerator pg;
  while (true) {
    idtable.length = cursize;
    logln("Try ", cursize);
    idtable[] = Init!(Stuple!(void*, int));
    pg.reset;
    refactor:
    auto factor = pg.gen();
    if (factor > 1024) { logln("Cancel factors, big break"); break; }
    foreach (entry; ci) {
      auto pos = ((cast(size_t) cast(void*) entry) >> 3) * factor;
      if (idtable[pos]._0) { logln("collision found for ", factor, "; size ", idtable.length); goto refactor; }
    }
    cursize --;
  }
  asm { int 3; }
}

static this() { initTable; }

int getId(ClassInfo ci) {
  return -1;
}

struct _fastcast(T) {
  const ptrdiff_t INVALID = 0xffff; // magic numbah
  static ptrdiff_t[quicklist.length] offsets;
  T opCall(U)(U u) {
    if (!u) return null;
    // logln("Cast ", (cast(Object) u).classinfo.name);
    Object obj;
    static if (!is(U: Object)) { // interface
      auto ptr = **cast(Interface***) u;
      obj = cast(Object) (cast(void*) u - ptr.offset);
    } else {
      obj = u;
    }
    auto id = getId(obj.classinfo);
    if (id == -1) return cast(T) u;
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
