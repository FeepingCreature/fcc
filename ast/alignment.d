module ast.alignment;

import ast.base, ast.structure, ast.vardecl,
  ast.namespace, ast.vector, ast.modules, ast.assign;

class UnAlignedPlaceholder : IType {
  IType base;
  this(IType base) { this.base = base; }
  override {
    string llvmType() { return base.llvmType(); }
    string llvmSize() { return base.llvmSize(); }
    string mangle() { return base.mangle; }
    int opEquals(IType it) {
      if (auto uap = fastcast!(UnAlignedPlaceholder) (it))
      return base.opEquals(uap.base);
      return base.opEquals(it);
    }
    IType proxyType() { return null; }
    bool isPointerLess() { return base.isPointerLess(); }
    bool isComplete() { return base.isComplete(); }
    string toString() { return qformat("unaligned ", base); }
  }
}

// TODO: change function call api to allow aligned parameters internally
// NEEDED_FOR SSE support
extern(C) void alignment_emitAligned(Expr ex, LLVMFile lf) {
  todo("alignment_emitAligned");
  /*mixin(mustOffset("ex.valueType().size"[]));
  if (auto al = fastcast!(ForceAlignment) (resolveType(ex.valueType()))) {
    auto myAl = al.alignment();
    if (myAl && ((lf.currentStackDepth + esp_alignment_delta + ex.valueType().size) % myAl) != 0) {
      // need realignment
      mkVar(lf, fastalloc!(UnAlignedPlaceholder)(ex.valueType()), true, (Variable var) {
        emitAssign(lf, var, ex);
      });
      return;
    }
  }
  ex.emitLLVM(lf);*/
}
