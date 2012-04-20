module ast.alignment;

import ast.base, ast.structure, ast.vardecl,
  ast.namespace, ast.vector, ast.modules, ast.assign;

extern(C) int align_boffs(IType t, int curdepth = -1) {
  if (curdepth == -1) {
    auto sl = namespace().get!(ScopeLike);
    if (!sl) {
      logln("no ScopeLike beneath "[], namespace(), " for placing a "[], t);
      fail;
    }
    curdepth = sl.framesize();
  }
  if (curdepth == -1) {
    logln("Could not align "[], t, ": insufficient framesize information from "[], namespace().get!(ScopeLike));
    fail;
  }
  int sz = t.size;
  int offs = curdepth + sz;
  doAlign(offs, t);
  if (isARM && sz == 1) offs = (offs + 3) & ~3; // make sure sp stays aligned
  return -offs;
}

class UnAlignedPlaceholder : IType {
  IType base;
  this(IType base) { this.base = base; }
  override {
    int size() { return base.size; }
    override string mangle() { return base.mangle; }
    ubyte[] initval() { return base.initval(); }
    int opEquals(IType it) { return base.opEquals(it); }
    IType proxyType() { return null; }
    bool isPointerLess() { return base.isPointerLess(); }
    bool isComplete() { return base.isComplete(); }
  }
}

// TODO: change function call api to allow aligned parameters internally
// NEEDED_FOR SSE support
extern(C) void alignment_emitAligned(Expr ex, AsmFile af) {
  mixin(mustOffset("ex.valueType().size"[]));
  if (auto al = fastcast!(ForceAlignment) (resolveType(ex.valueType()))) {
    auto myAl = al.alignment();
    if (myAl && ((af.currentStackDepth + ex.valueType().size) % myAl) != 0) {
      // need realignment
      mkVar(af, fastalloc!(UnAlignedPlaceholder)(ex.valueType()), true, (Variable var) {
        (fastalloc!(Assignment)(var, ex)).emitAsm(af);
      });
      return;
    }
  }
  ex.emitAsm(af);
}
