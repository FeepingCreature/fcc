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

import ast.modules;
Object gotExtern(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("extern(C)")) return null;
  string tx;
  bool grabFun() {
    auto fun = new Function;
    fun.extern_c = true;
    New(fun.type);
    auto t3 = t2;
    if (test(fun.type.ret = fastcast!(IType)~ rest(t3, "type")) &&
        t3.gotIdentifier(fun.name) &&
        t3.gotParlist(fun.type.params, rest) &&
        t3.accept(";")
      )
    {
      t2 = t3;
      namespace().add(fun);
      return true;
    } else {
      tx = t3;
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
      tx = t3;
      return false;
    }
  }
  bool grabFunDef() {
    auto t3 = t2;
    Function fun;
    if (!rest(t3, "tree.fundef", &fun)) return false;
    fun.extern_c = true;
    logln("got fundef ", fun.name);
    current_module().entries ~= fun;
    t2 = t3;
    return true;
  }
  void fail() {
    tx.failparse("extern parsing failed");
  }
  if (t2.accept("{")) {
    while (grabFun() || grabVar() || grabFunDef()) { }
    if (!t2.accept("}")) fail;
  } else if (!grabFun() && !grabVar() && !grabFunDef()) fail;
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotExtern, "tree.toplevel.extern_c");
