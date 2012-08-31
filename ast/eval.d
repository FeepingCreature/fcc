module ast.eval;

import ast.base, ast.fun;

Object gotEval(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Object obj;
  if (!rest(t2, "tree.expr"[], &obj))
    return null;
    // t2.failparse("Could not parse expr"[]);
  
  if (auto ex = fastcast!(Expr) (obj))
    obj = fastcast!(Object) (forcedConvert(ex));
  
  text = t2;
  if (auto fun = fastcast!(Function)~ obj) {
    if (fun.getParams().length)
      throw new Exception("Cannot evaluate function with parameters! "[]);
    return fun.mkCall();
  }
  return obj;
}
mixin DefaultParser!(gotEval, "tree.expr.eval"[], "27"[], "evaluate"[]);
