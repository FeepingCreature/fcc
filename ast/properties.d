module ast.properties;

import ast.base, ast.parse, ast.casting, ast.tuples;

import tools.log;
Object gotProperties(bool withTuple)(ref string text, ParseCb cont, ParseCb rest) {
  // check all possible continuations
  string longest; Object res;
  Object obj;
  cont(text, &obj);
  if (!obj) return null;
  auto ex = cast(Expr) obj;
  static if (withTuple) {
    if (!ex || !cast(Tuple) ex.valueType())
      return null; // don't.
  } else {
    if (!ex || cast(Tuple) ex.valueType())
      return null; // just .. don't.
  }
  
  void check(Object sup, string text) {
    auto backup = lhs_partial();
    scope(exit) lhs_partial.set(backup);
    
    lhs_partial.set(sup);
    auto t2 = text;
    
    bool matched;
    while (true) {
      if (auto nl = rest(t2, "tree.rhs_partial")) {
        matched = true;
        lhs_partial.set(nl);
      } else break;
    }
    
    if (matched) {
      if (auto ex = cast(Expr) lhs_partial()) {
        // hit a snag, try to mutate
        gotImplicitCast(ex, (Expr ex) { check(cast(Object) ex, t2); return false; });
      }
      if (t2.ptr > longest.ptr) {
        longest = t2;
        res = lhs_partial();
      }
    }
  }
  
  if (auto ex = cast(Expr) obj) {
    gotImplicitCast(ex, (Expr ex) { check(cast(Object) ex, text); return false; });
  } else check(obj, text);
  
  assert(!res || longest);
  if (longest) text = longest;
  return res;
}
mixin DefaultParser!(gotProperties!(true), "tree.expr.properties.tup", "0");
mixin DefaultParser!(gotProperties!(false), "tree.expr.properties.no_tup", "1");
static this() { parsecon.addPrecedence("tree.expr.properties", "240"); }
