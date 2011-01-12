module ast.properties;

import ast.base, ast.parse, ast.casting, ast.tuples: AstTuple = Tuple;

struct PropArgs {
  bool withTuple = true, withCall = true;
}

TLS!(PropArgs) propcfg;

static this() { New(propcfg); }

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
  auto ex = cast(Expr) obj;
  if (!myArgs.withTuple) {
    if (ex && cast(AstTuple) ex.valueType())
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
      string match = "tree.rhs_partial";
      if (!myArgs.withCall)
        match ~= " >tree.rhs_partial.funcall";
      if (auto nl = rest(t2, match)) {
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
mixin DefaultParser!(gotProperties, "tree.expr.properties", "240");
