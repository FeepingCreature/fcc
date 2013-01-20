module ast.properties_parse;

import ast.base, ast.fun, ast.properties, ast.parse, ast.casting, ast.math;

import tools.base, tools.log;
Object getProperties(ref string text, Object sup, PropArgs args,
  ParseCb cont, ParseCb rest, bool rawmode = false)
{
  auto withTuple = args.withTuple;
  auto withCall = args.withCall;
  auto withCallOnTuple = args.withCallOnTuple;
  string longest; Object res;
  // check all possible continuations
  
  bool isTuple;
  auto ex = fastcast!(Expr) (sup);
  if (ex && fastcast!(AstTuple) (ex.valueType()))
    if (!withTuple)
      return null; // don't
    else
      isTuple = true;
  
  void cleanup(ref Object obj) {
    if (auto ex = fastcast!(Expr) (obj)) {
      ex = forcedConvert(ex);
      obj = fastcast!(Object) (ex);
    }
  }
  
  // logln("prop match for "[], sup, " @"[], text.nextText());
  void check(Object sup, string text) {
    auto backup = lhs_partial();
    scope(exit) lhs_partial.set(backup);
    
    cleanup(sup);
    lhs_partial.set(sup);
    auto t2 = text;
    
    bool matched;
    while (true) {
      auto t3 = t2;
      // terminators
      if (t3.accept("="[]) || t3.accept(")"[]) || t3.accept("!="[]) || t3.accept("+"[]) || t3.accept("/"[])) {
        break;
      }
      if (rawmode || !fastcast!(Function) (sup) && !fastcast!(OverloadSet) (sup) && t3.accept(";"[])) {
        break;
      }
      string match = "tree.rhs_partial";
      if (!withCall || !withCallOnTuple && isTuple)
        match ~= " >tree.rhs_partial.funcall >tree.rhs_partial.fpz_dgcall";
      if (auto nl = rest(t2, match)) {
        matched = true;
        cleanup(nl);
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
  } else */if (!rawmode) check(sup, text);
  
  assert(!res || longest);
  if (longest) {
    auto t2 = longest;
    if (t2.accept(".") && !t2.accept("."))
      longest.failparse("unknown property or identifier");
    text = longest;
  }
  return res;
}

void withPropcfg(void delegate(PropArgs) dg) {
  auto myArgs = *propcfg.ptr();
  *propcfg.ptr() = Init!(PropArgs);
  scope(exit) *propcfg.ptr() = myArgs;
  dg(myArgs);
}

static this() {
  getPropertiesFn = &getProperties;
  withPropcfgFn = &withPropcfg;
}

Object gotProperties(ref string text, ParseCb cont, ParseCb rest) {
  auto backupPB = *currentPropBase.ptr();
  scope(exit) *currentPropBase.ptr() = backupPB;
  
  *currentPropBase.ptr() = text;
  
  auto rawmode = text.rawmode();
  
  Object res;
  withPropcfg((PropArgs args) {
    Object sup;
    if (!cont(text, &sup)) return;
    res = getProperties(text, sup, args, cont, rest, rawmode);
  });
  return res;
}
mixin DefaultParser!(gotProperties, "tree.expr.properties"[], "240"[]);
