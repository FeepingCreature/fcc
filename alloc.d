module alloc;

import tools.base, tools.log, tools.threads;

extern(C) Stuple!(void[], int)* get_memory_ptr();
// TLS!(void[]) _memory;
// TLS!(int) _lastsize;
// static this() { New(_memory); New(_lastsize); }
import std.gc;

void* allocate(void[] init) {
  auto sz = init.length;
  auto mp = get_memory_ptr();
  auto memory = mp._0;
  if (memory.length < sz) {
    /*
    auto p = _lastsize.ptr();
    int blksz = *p * 2;
    if (!blksz) blksz = 16384;
    *p = blksz;
    memory = new void[blksz];*/
    // memory = new void[8192];
    memory = (cast(void*) std.c.stdlib.malloc(1048576))[0..1048576];
    addRange(memory.ptr, memory.ptr + memory.length);
  }
  auto data = memory[0..sz];
  memory = memory[sz .. $];
  mp._0 = memory;
  data[] = init;
  return data.ptr;
}

/*const string opttypes = `
  Pointer, ReinterpretCast, ExtArray, FirstParamOverrideSpace, MyPlaceholderExpr, AsmIntBinopExpr, RelMember, StaticArray
`;*/
const string opttypes = `
  FirstParamOverrideSpace, Structure, MiniNamespace, RelFunction, ReinterpretCast, Scope, Pointer, ClassRef, RelMember, StaticArray, Function, FunctionPointer, PointerFunction,
  Tuple, DerefExpr, MemberAccess_LValue, MyPlaceholderExpr, MemberAccess_Expr, DgCallable, Symbol, FunSymbol, PrefixFunction, IntfRef, RefExpr, ExprAlias,
  LazyDeltaInt, TypeAlias
`;

string fixstring(string s) {
  while (true) {
    string pre = ctSlice(s, ".");
    if (!s.length) return pre;
  }
}

string genCondition() {
  string s = opttypes;
  string res = "false";
  while (true) {
    string match = ctSlice(s, ",").ctStrip();
    if (!match.length) break;
    res ~= " || (fixstring(T.stringof) == \""~match~"\")";
  }
  return res;
}

template fastalloc(T) {
  T fastalloc(U...)(U u) {
    // use of class allocator actually gives negligible to no benefit.
    // so keep it off for now.
    // return new T(u);
    T res;
    mixin("static if ("~genCondition()~") {
      // logln(\"## \", T.stringof);
      res = cast(T) allocate(T.classinfo.init);
      res = res._ctor(u);
    } else {
      res = new T(u);
    }");
    return res;
  }
}
