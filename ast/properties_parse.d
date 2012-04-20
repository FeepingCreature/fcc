module ast.properties_parse;

import ast.base, ast.fun, ast.properties, ast.parse, ast.casting, ast.math;

import tools.base, tools.log;
Object getProperties(ref string text, Object sup, bool withTuple, bool withCall,
  ParseCb cont, ParseCb rest)
{
  string longest; Object res;
  // check all possible continuations
  auto ex = fastcast!(Expr)~ sup;
  if (!withTuple) {
    if (ex && fastcast!(AstTuple) (ex.valueType()))
      return null; // don't
  }
  
  // logln("prop match for "[], sup, " @"[], text.nextText());
  void check(Object sup, string text) {
    auto backup = lhs_partial();
    scope(exit) lhs_partial.set(backup);
    
    lhs_partial.set(sup);
    auto t2 = text;
    
    bool matched;
    while (true) {
      auto t3 = t2;
      // terminators
      if (t3.accept("="[]) || t3.accept(")"[]) || t3.accept("!="[]) || t3.accept("+"[]) || t3.accept("/"[])) {
        break;
      }
      if (!fastcast!(Function) (sup) && !fastcast!(OverloadSet) (sup) && t3.accept(";"[])) {
        break;
      }
      string match = "tree.rhs_partial";
      if (!withCall)
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
  
  /*if (auto ex = fastcast!(Expr)~ sup) {
    gotImplicitCast(ex, (Expr ex) { check(fastcast!(Object)~ ex, text); return false; });
  } else */check(sup, text);
  
  assert(!res || longest);
  if (longest) text = longest;
  return res;
}

void withPropcfg(void delegate(bool, bool) dg) {
  auto myArgs = *propcfg.ptr();
  *propcfg.ptr() = Init!(PropArgs);
  scope(exit) *propcfg.ptr() = myArgs;
  dg(myArgs.withTuple, myArgs.withCall);
}

static this() {
  getPropertiesFn = &getProperties;
  withPropcfgFn = &withPropcfg;
}

Object gotProperties(ref string text, ParseCb cont, ParseCb rest) {
  auto backupPB = *currentPropBase.ptr();
  scope(exit) *currentPropBase.ptr() = backupPB;
  
  *currentPropBase.ptr() = text;
  
  Object res;
  withPropcfg((bool withTuple, bool withCall) {
    Object sup;
    if (!cont(text, &sup)) return;
    res = getProperties(text, sup, withTuple, withCall, cont, rest);
  });
  return res;
}
mixin DefaultParser!(gotProperties, "tree.expr.properties"[], "240"[]);
