module ast.guard;

import
  ast.parse, ast.base, ast.namespace, ast.scopes,
  ast.assign, ast.nestfun, ast.modules;

Object gotGuard(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("onExit")) return null;
  string type = "onExit";
  Statement st;
  auto t3 = t2, t4 = t2;
  auto sc = cast(Scope) namespace();
  assert(sc, Format("::", namespace()));
  
  if (type == "onSuccess" || type == "onExit") {
    if (!rest(t3, "tree.stmt", &st))
      throw new Exception("No statement matched for "~type~" in scope context: "~t3.next_text());
    sc.guards ~= st;
  }
  if (type == "onFailure" || type == "onExit") {
    auto nf = new NestedFunction(sc), mod = sc.get!(Module)();
    New(nf.type);
    nf.type.ret = Single!(Void);
    nf.fixup;
    nf.sup = mod;
    static int funId;
    nf.name = Format("guardfn_", funId++);
    auto backup = sc;
    scope(exit) namespace.set(backup);
    namespace.set(nf);
    if (!rest(t4, "tree.scope", &nf.tree))
      throw new Exception("No statement matched for "~type~" in exception guard context: "~t4.next_text());
    mod.entries ~= cast(Tree) nf;
    // TODO: build linked list here
    // TODO: remove from stack on scope exit (add guard, lol)
  }
  
  assert(t3 is t4);
  text = t3;
  return Single!(NoOp);
}
mixin DefaultParser!(gotGuard, "tree.stmt.guard");

interface IScoped {
  Expr getSup();
  void emitAsmStart(AsmFile af);
  void emitAsmEnd(AsmFile af);
}

class Scoped(T) : T, IScoped {
  T sup;
  static assert(is(T: LValue) || is(T: MValue));
  this(T t) { sup = t; }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(sup);
  override {
    void emitAsm(AsmFile af) { assert(false); }
    IType valueType() { return sup.valueType(); }
    Expr getSup() { return sup; }
    void emitAsmStart(AsmFile af) { sup.emitAsm(af); }
    static if (is(T: LValue)) {
      void emitLocation(AsmFile af) { assert(false); }
      void emitAsmEnd(AsmFile af) {
        (new Assignment(sup, new Placeholder(sup.valueType()))).emitAsm(af);
      }
    }
    static if (is(T: MValue)) {
      void emitAssignment(AsmFile af) { assert(false); }
      void emitAsmEnd(AsmFile af) {
        sup.emitAssignment(af);
      }
    }
  }
}

Expr genScoped(Expr ex) {
  if (auto mv = cast(MValue) ex) return new Scoped!(MValue)(mv);
  if (auto lv = cast(LValue) ex) return new Scoped!(LValue)(lv);
  throw new Exception(Format("cannot scope ", ex));
}

import tools.log;
Object gotScoped(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("scoped")) return null;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex))
    throw new Exception("Failed to match expr for scoped at '"~t2.next_text()~"'. ");
  text = t2;
  return cast(Object) genScoped(ex);
}
mixin DefaultParser!(gotScoped, "tree.expr.scoped", "26");
