module ast.externs;

import ast.base, ast.fun, ast.namespace;

Object gotExtern(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("extern(C)")) return null;
  bool grabFun() {
    auto fun = new Function;
    fun.extern_c = true;
    New(fun.type);
    if (test(fun.type.ret = cast(IType) rest(t2, "type")) &&
        t2.gotIdentifier(fun.name) &&
        t2.gotParlist(fun.type.params, rest) &&
        t2.accept(";")
      )
    {
      namespace().add(fun);
      return true;
    } else {
      return false;
    }
  }
  void fail() {
    assert(false, "extern parsing failed at '"~t2.next_text()~"'.");
  }
  if (t2.accept("{")) {
    while (grabFun()) { }
    if (!t2.accept("}")) fail;
  } else if (!grabFun()) fail;
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotExtern, "tree.toplevel.extern_c");
