module ast.withstmt;

import ast.base, ast.parse, ast.vardecl, ast.namespace;

class WithStmt : Namespace, Statement {
  RelNamespace ns;
  VarDecl vd;
  Expr context;
  Statement sub;
  mixin defaultIterate!(vd, sub);
  this(Expr ex) {
    ns = cast(RelNamespace) ex.valueType();
    assert(ns, Format("Cannot with-expr a non-relns: ", ex.valueType())); // TODO: select in gotWithStmt
    if (auto lv = cast(LValue) ex) {
      context = lv;
    } else {
      auto var = new Variable;
      var.type = ex.valueType();
      var.initval = ex;
      var.baseOffset = boffs(var.type);
      context = var;
      New(vd);
      vd.vars ~= var;
    }
    sup = namespace();
  }
  override {
    void emitAsm(AsmFile af) {
      auto checkpt = af.checkptStack();
      if (vd)
        vd.emitAsm(af);
      sub.emitAsm(af);
      af.restoreCheckptStack(checkpt);
    }
    string mangle(string name, IType type) { assert(false); }
    Stuple!(IType, string, int)[] stackframe() { assert(false); }
    Object lookup(string name, bool local = false) {
      if (auto res = ns.lookupRel(name, context))
        return res;
      if (local) return null;
      return sup.lookup(name);
    }
  }
}

Object gotWithStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("with")) return null;
  Expr ex;
  if (!rest(t2, "tree.expr", &ex)) throw new Exception("Couldn't match with-expr at "~t2.next_text());
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  auto ws = new WithStmt(ex);
  namespace.set(ws);
  if (!rest(t2, "tree.stmt", &ws.sub)) throw new Exception("Couldn't match with-body at "~t2.next_text());
  text = t2;
  return ws;
}
mixin DefaultParser!(gotWithStmt, "tree.stmt.withstmt");
