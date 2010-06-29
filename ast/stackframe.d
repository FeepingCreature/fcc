module ast.stackframe;

import ast.namespace, ast.structure, ast.namespace, ast.base, ast.int_literal, ast.casting, ast.pointer, ast.math;

import tools.base, quicksort;
LValue namespaceToStruct(Namespace ns, Expr baseptr) {
  auto frame = ns.stackframe().dup;
  qsort(frame, ex!("a, b -> a._2 < b._2"));
  assert(frame[0]._2 < frame[1]._2);
  auto str = new Structure(null);
  auto cur = -1;
  foreach (member; frame) {
    new StructMember(member._1, member._0, str);
    if (cur == -1) cur = member._2;
    else assert(cur == member._2);
    cur += member._0.size;
  }
  logln("final cur: ", cur, ", start ", -frame[0]._2);
  // return *(stack_struct_type*) (ebp - lowestvar_offset);
  return new DerefExpr(
    new ReinterpretCast!(Expr)(
      new Pointer(str),
      new SubExpr(baseptr, new IntExpr(-frame[0]._2))
    )
  );
}
