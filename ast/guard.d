module ast.guard;

import ast.parse, ast.base, ast.namespace, ast.scopes, ast.assign;

Object gotGuard(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("atexit")) return null;
  Statement st;
  if (!rest(t2, "tree.stmt", &st)) throw new Exception("No statement matched for atexit: "~t2.next_text());
  auto sc = cast(Scope) namespace();
  assert(sc, Format("::", namespace()));
  sc.guards ~= st;
  text = t2;
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
  this(T t) { sup = t; }
  static assert(is(T: LValue) || is(T: MValue));
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
