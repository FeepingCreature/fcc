module ast.alignment;

import ast.base, ast.structure, ast.vardecl, ast.namespace, ast.vector, ast.modules;

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
