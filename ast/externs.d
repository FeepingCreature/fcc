module ast.externs;

import ast.base, ast.fun, ast.namespace;

class ExternCGlobVar : Expr, Named {
  IType type;
  string name;
  mixin defaultIterate!();
  ExternCGlobVar dup() { return this; /* invariant */ }
  this(IType t, string n) {
    this.type = t;
    this.name = n;
  }
  override {
    IType valueType() { return type; }
    string getIdentifier() { return name; }
    void emitAsm(AsmFile af) {
      af.pushStack(name, type);
    }
    string toString() { return Format("extern(C) global ", name, " of ", type); }
  }
}

Object gotExtern(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("extern(C)")) return null;
  bool grabFun() {
    auto fun = new Function;
    fun.extern_c = true;
    New(fun.type);
    auto t3 = t2;
    if (test(fun.type.ret = cast(IType) rest(t3, "type")) &&
        t3.gotIdentifier(fun.name) &&
        t3.gotParlist(fun.type.params, rest) &&
        t3.accept(";")
      )
    {
      t2 = t3;
      namespace().add(fun);
      return true;
    } else {
      return false;
    }
  }
  bool grabVar() {
    auto t3 = t2;
    IType type; string name;
    if (rest(t3, "type", &type) && t3.gotIdentifier(name) && t3.accept(";")) {
      t2 = t3;
      auto gv = new ExternCGlobVar(type, name);
      namespace().add(gv);
      return true;
    } else {
      return false;
    }
  }
  void fail() {
    assert(false, "extern parsing failed at '"~t2.next_text()~"'.");
  }
  if (t2.accept("{")) {
    while (grabFun() || grabVar()) { }
    if (!t2.accept("}")) fail;
  } else if (!grabFun() && !grabVar()) fail;
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotExtern, "tree.toplevel.extern_c");
