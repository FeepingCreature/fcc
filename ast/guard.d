module ast.guard;

import ast.parse, ast.base, ast.namespace, ast.scopes;

Object gotGuard(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("atexit")) return null;
  Statement st;
  if (!rest(t2, "tree.stmt", &st)) throw new Exception("No statement matched for atexit: "~t2.next_text());
  auto sc = cast(Scope) namespace();
  assert(sc, Format("::", namespace()));
  sc.guards ~= st;
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotGuard, "tree.stmt.guard");
