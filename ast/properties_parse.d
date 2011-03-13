module ast.properties_parse;

import ast.base, ast.fun, ast.properties, ast.parse, ast.casting;

import tools.base, tools.log;
Object gotProperties(ref string text, ParseCb cont, ParseCb rest) {
  string longest; Object res;
  auto myArgs = *propcfg.ptr();
  *propcfg.ptr() = Init!(PropArgs);
  scope(exit) *propcfg.ptr() = myArgs; // reset 1
  // check all possible continuations
  Object obj;
  cont(text, &obj);
  if (!obj) return null;
  auto ex = fastcast!(Expr)~ obj;
  if (!myArgs.withTuple) {
    if (ex && fastcast!(AstTuple)~ ex.valueType())
      return null; // don't
  }
  
  // logln("prop match for ", obj, " @", text.nextText());
  void check(Object sup, string text) {
    auto backup = lhs_partial();
    scope(exit) lhs_partial.set(backup);
    
    lhs_partial.set(sup);
    auto t2 = text;
    
    bool matched;
    while (true) {
      auto t3 = t2;
      // terminators
      if (t3.accept("=") || t3.accept(")") || t3.accept("!=") || t3.accept("+") || t3.accept("/")) {
        break;
      }
      if (!fastcast!(Function) (sup) && t3.accept(";")) {
        break;
      }
      string match = "tree.rhs_partial";
      if (!myArgs.withCall)
        match ~= " >tree.rhs_partial.funcall";
      if (auto nl = rest(t2, match)) {
        matched = true;
        lhs_partial.set(nl);
        sup = nl;
      } else break;
    }
    
    if (matched) {
      if (auto ex = fastcast!(Expr)~ lhs_partial()) {
        // hit a snag, try to mutate
        // Yeah, how about no. 
        // gotImplicitCast(ex, (Expr ex) { check(fastcast!(Object)~ ex, t2); return false; });
      }
      if (t2.ptr > longest.ptr) {
        longest = t2;
        res = lhs_partial();
      }
    }
  }
  
  /*if (auto ex = fastcast!(Expr)~ obj) {
    gotImplicitCast(ex, (Expr ex) { check(fastcast!(Object)~ ex, text); return false; });
  } else */check(obj, text);
  
  assert(!res || longest);
  if (longest) text = longest;
  return res;
}
mixin DefaultParser!(gotProperties, "tree.expr.properties", "240");
