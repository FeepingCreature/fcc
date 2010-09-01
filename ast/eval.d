module ast.eval;

import ast.base, ast.fun;

Object gotEval(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("eval")) return null;
  Object obj;
  if (!rest(t2, "tree.expr", &obj))
    throw new Exception("Could not parse expr at '"~t2.next_text()~"'. ");
  text = t2;
  if (auto fun = cast(Function) obj) {
    if (fun.type.params.length)
      throw new Exception("Cannot evaluate function with parameters! ");
    return fun.mkCall();
  }
  return obj;
}
mixin DefaultParser!(gotEval, "tree.expr.eval", "27");
