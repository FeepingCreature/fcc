module ast.scopes;

import ast.base, ast.namespace, ast.fun, ast.variable, parseBase, tools.base: apply;

import ast.aggregate;
class Scope : Namespace, Tree, ScopeLike, Statement {
  Function fun;
  Statement _body;
  Statement[] guards;
  ulong id;
  mixin defaultIterate!(_body, guards);
  Statement[] getGuards() {
    if (auto sc = cast(Scope) sup) return sc.getGuards() ~ guards;
    else return guards;
  }
  void addStatement(Statement st) {
    if (auto as = cast(AggrStatement) _body) as.stmts ~= st;
    else if (!_body) _body = st;
    else {
      auto as = new AggrStatement;
      as.stmts ~= _body;
      as.stmts ~= st;
      _body = as;
    }
  }
  string base() {
    if (fun) return fun.mangleSelf();
    return sup.mangle("scope", null);
  }
  string entry() { return Format(base, "_entry", id); }
  string exit() { return Format(base, "_exit", id); }
  string toString() { return Format("scope <- ", sup); }
  this() {
    id = getuid();
    sup = namespace();
    fun = sup.get!(Function);
  }
  override int framesize() {
    // TODO: alignment
    int res;
    foreach (obj; field) {
      if (auto var = cast(Variable) obj._1) {
        res += var.type.size;
      }
    }
    if (auto sl = cast(ScopeLike) sup)
      res += sl.framesize();
    return res;
  }
  // frame offset caused by parameters
  int framestart() {
    assert(!!fun);
    return fun.framestart();
  }
  // continuations good
  void delegate(bool=false) delegate() open(AsmFile af) {
    af.emitLabel(entry());
    auto checkpt = af.checkptStack(), backup = namespace();
    namespace.set(this);
    return stuple(checkpt, backup, this, af) /apply/ (typeof(checkpt) checkpt, typeof(backup) backup, typeof(this) that, AsmFile af) {
      that._body.emitAsm(af);
      return stuple(checkpt, that, backup, af) /apply/ (typeof(checkpt) checkpt, typeof(that) that, typeof(backup) backup, AsmFile af, bool onlyCleanup) {
        if (!onlyCleanup) af.emitLabel(that.exit());
        
        foreach_reverse(guard; that.guards)
          guard.emitAsm(af);
        
        af.restoreCheckptStack(checkpt);
        if (!onlyCleanup) namespace.set(backup);
      };
    };
  }
  override {
    void emitAsm(AsmFile af) {
      open(af)()(); // lol
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, local);
      // TODO: &&? ||? WHO KNOWS =D
      // if (!res && cast(Scope) sup)
      if (res) return res;
      return sup.lookup(name, local);
    }
    string mangle(string name, IType type) {
      return sup.mangle(name, type) ~ "_local";
    }
    Stuple!(IType, string, int)[] stackframe() {
      typeof(sup.stackframe()) res;
      if (sup) res = sup.stackframe();
      foreach (obj; field)
        if (auto var = cast(Variable) obj._1)
          res ~= stuple(var.type, var.name, var.baseOffset);
      return res;
    }
  }
}

Object gotScope(ref string text, ParseCb cont, ParseCb rest) {
  if (auto res = rest(text, "tree.stmt.aggregate")) return res; // always scope anyway
  auto sc = new Scope;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto t2 = text;
  if (rest(t2, "tree.stmt", &sc._body)) { text = t2; return sc; }
  throw new Exception("Couldn't match scope off "~text.next_text());
}
mixin DefaultParser!(gotScope, "tree.scope");
