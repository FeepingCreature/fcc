module fastalloc;

import tools.base, tools.log, tools.threads;

TLS!(void[]) _memory;
TLS!(int) _lastsize;
static this() { New(_memory); New(_lastsize); }

void* allocate(void[] init) {
  auto sz = init.length;
  auto memory = *_memory.ptr();
  if (memory.length < sz) {
    /*
    auto p = _lastsize.ptr();
    int blksz = *p * 2;
    if (!blksz) blksz = 16384;
    *p = blksz;
    memory = new void[blksz];*/
    memory = new void[8192];
  }
  auto data = memory[0..sz];
  memory = memory[sz .. $];
  *_memory.ptr() = memory;
  data[] = init;
  return data.ptr;
}

const string opttypes = `
  Pointer, ReinterpretCast, ExtArray, FirstParamOverrideSpace, MyPlaceholderExpr, AsmIntBinopExpr, RelMember, StaticArray
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
