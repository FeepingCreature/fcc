module ast.stackframe;

import ast.namespace, ast.structure, ast.namespace, ast.base, ast.int_literal, ast.casting, ast.pointer, ast.opers;

import quicksort;
LValue scopelikeToStruct(ScopeLike sl, Expr baseptr) {
  auto frame = sl.stackframe();
  logln("scopelikeToStruct on ", frame);
  todo("scopelikeToStruct");
  return null;
  /*assert(frame[0]._2 < frame[1]._2);
  auto str = fastalloc!(Structure)(cast(string) null);
  // nu! stack variables are aligned now.
  // str.packed = true; // !!
  int lastPos = -1;
  RelMember lastMember;
  foreach (member; frame) {
    auto rm = fastalloc!(RelMember)(member._1, member._0, str);
    // make sure it has the same layout as the stackframe
    // note: structs are constructed forwards, stackframes backwards!
    if (lastPos == -1) { lastPos = member._2; lastMember = rm; }
    else {
      auto delta = member._2 - lastPos;
      rm.offset = lastMember.offset + delta;
      lastPos = member._2;
      lastMember = rm;
    }
  }
  // logln("offset: "[], baseptr, " - -"[], frame[0], " .... "[], frame[1..$], " struct "[], str);
  return fastalloc!(DerefExpr)(
    new ReinterpretCast!(Expr)(
      fastalloc!(Pointer)(str),
      lookupOp("-"[], baseptr, mkInt(-frame[0]._2))
    )
  );*/
}
