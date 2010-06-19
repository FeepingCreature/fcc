module ast.stackframe;

import ast.namespace, ast.structure, ast.scopes, ast.base, ast.int_literal, ast.casting, ast.pointer, ast.math;

import tools.base, quicksort;
LValue scopeToStruct(Scope sc, Expr baseptr) {
  auto m = sc.members();
  qsort(m, ex!("a, b -> a._2 < b._2"));
  assert(m[0]._2 < m[1]._2);
  Structure.Member[] field;
  auto cur = -1;
  foreach (member; m) {
    field ~= Structure.Member(member._1, member._0);
    if (cur == -1) cur = member._2;
    else assert(cur == member._2);
    cur += member._0.size;
  }
  assert(!cur); // integrity check
  // return *(stack_struct_type*) (ebp - lowestvar_offset);
  return new DerefExpr(
    new ReinterpretCast!(Expr)(
      new Pointer(new Structure(null, field)),
      new SubExpr(baseptr, new IntExpr(-m[0]._2))
    )
  );
}
