module ast.properties;

import ast.base, ast.parse, ast.casting, ast.tuples: AstTuple = Tuple;

struct PropArgs {
  bool withTuple = true, withCall = true;
}

TLS!(PropArgs) propcfg;

static this() { New(propcfg); }
