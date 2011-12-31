module ast.externs;

import ast.base, ast.fun, ast.namespace, ast.pointer;

static int arm_var_fixup_count;
class ExternCGlobVar : LValue, Named {
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
      if (isARM) {
        if (type.size != 4) fail;
        af.mmove4(qformat("=", name), "r0");
        af.mmove4("[r0]", "r0");
        af.pushStack("r0", 4);
      } else {
        af.pushStack(name, type.size);
      }
    }
    void emitLocation(AsmFile af) {
      if (isARM) {
        af.loadAddress(qformat("#", name), "r0");
        af.pushStack("r0", 4);
      } else {
        af.pushStack(qformat("$", name), nativePtrSize);
      }
    }
    string toString() { return Format("extern(C) global ", name, " of ", type); }
  }
}

Object gotMarkStdCall(ref string text, ParseCb cont, ParseCb rest) {
  IType ty;
  if (!rest(text, "type", &ty))
    text.failparse("Expected type to mark as std-call. ");
  auto fp = fastcast!(FunctionPointer) (resolveType(ty));
  if (!fp)
    text.failparse(ty, " is not a function pointer! ");
  auto fp2 = new FunctionPointer;
  fp2.ret = fp.ret;
  fp2.args = fp.args;
  fp2.stdcall = true;
  return fp2;
}
mixin DefaultParser!(gotMarkStdCall, "type.mark_stdcall", "911", "_markStdCall");

import ast.modules;
Object gotExtern(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool isStdcall;
  if (!t2.accept("extern(")) return null;
  if (!t2.accept("C")) {
    if (!t2.accept("Windows")) return null;
    isStdcall = true;
  }
  if (!t2.accept(")")) return null;
  string tx;
  bool grabFun() {
    auto fun = new Function;
    fun.extern_c = true;
    New(fun.type);
    fun.type.stdcall = isStdcall;
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
    IType type; string n; string[] names;
    if (rest(t3, "type", &type) && t3.bjoin(t3.gotIdentifier(n), t3.accept(","), { names ~= n; }) && t3.accept(";")) {
      t2 = t3;
      foreach (name; names) {
        auto gv = new ExternCGlobVar(type, name);
        namespace().add(gv);
      }
      return true;
    } else {
      tx = t3;
      return false;
    }
  }
  bool grabFunDef() {
    auto t3 = t2;
    Function fun;
    if (!rest(t3, "tree.fundef_externc", &fun)) return false;
    // logln("got fundef ", fun.name);
    current_module().entries ~= fun;
    t2 = t3;
    return true;
  }
  bool fallthrough() {
    auto t3 = t2;
    Object obj;
    if (!rest(t3, "tree.toplevel", &obj)) return false;
    t2 = t3;
    return true;
  }
  void fail() {
    tx.failparse("extern parsing failed");
  }
  if (t2.accept("{")) {
    do {
      if (t2.accept("}")) goto success;
    } while (grabFun() || grabVar() || grabFunDef() || fallthrough());
    t2.failparse("Expected closing '}' for extern(C)!");
    success:;
  } else if (!grabFun() && !grabVar() && !grabFunDef()) fail;
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotExtern, "tree.toplevel.extern_c");
