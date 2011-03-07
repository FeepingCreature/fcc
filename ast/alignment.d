module ast.alignment;

import ast.base, ast.structure, ast.vardecl,
  ast.namespace, ast.vector, ast.modules, ast.assign;

extern(C) int align_boffs(IType t, int curdepth = -1) {
  if (curdepth == -1) {
    auto sl = namespace().get!(ScopeLike);
    if (!sl) {
      logln("no ScopeLike beneath ", namespace(), " for placing a ", t);
      asm { int 3; }
    }
    curdepth = sl.framesize();
  }
  int offs = curdepth + t.size;
  doAlign(offs, t);
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
  }
}

// TODO: change function call api to allow aligned parameters internally
// NEEDED_FOR SSE support
extern(C) void alignment_emitAligned(Expr ex, AsmFile af) {
  mixin(mustOffset("ex.valueType().size"));
  if (auto al = fastcast!(ForceAlignment) (resolveType(ex.valueType()))) {
    auto myAl = al.alignment();
    if (myAl && ((af.currentStackDepth + ex.valueType().size) % myAl) != 0) {
      // need realignment
      mkVar(af, new UnAlignedPlaceholder(ex.valueType()), true, (Variable var) {
        (new Assignment(var, ex)).emitAsm(af);
      });
      return;
    }
  }
  ex.emitAsm(af);
}
