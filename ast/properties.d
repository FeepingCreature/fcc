module ast.properties;

import ast.base, ast.parse, ast.casting, ast.tuples: AstTuple = Tuple;

struct PropArgs {
  bool withTuple = true, withCall = true;
}

TLS!(PropArgs) propcfg;

static this() { New(propcfg); }

// placed here to break import cycle
import ast.vardecl;
Object gotLVize(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  
  // behaves like a fun call
  auto backup = *propcfg.ptr();
  scope(exit) *propcfg.ptr() = backup;
  propcfg.ptr().withTuple = false;
  
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Expected expression for lvize");
  text = t2;
  return fastcast!(Object) (lvize(ex));
}
mixin DefaultParser!(gotLVize, "tree.expr.lvize", "24071", "lvize");
