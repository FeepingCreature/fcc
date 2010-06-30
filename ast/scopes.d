module ast.scopes;

import ast.base, ast.namespace, ast.fun, ast.variable, parseBase;

class Scope : Namespace, Tree {
  Function fun;
  Statement _body;
  ulong id;
  mixin defaultIterate!(_body);
  string entry() { return Format(fun.mangleSelf(), "_entry", id); }
  string exit() { return Format(fun.mangleSelf(), "_exit", id); }
  string toString() { return Format("scope <- ", sup); }
  this() { id = getuid(); }
  import tools.log;
  int framesize() {
    // TODO: alignment
    int res;
    foreach (obj; field) {
      if (auto var = cast(Variable) obj._1) {
        res += var.type.size;
      }
    }
    if (auto sc = cast(Scope) sup)
      res += sc.framesize();
    return res;
  }
  // frame offset caused by parameters
  int framestart() {
    return fun.framestart();
  }
  override {
    void emitAsm(AsmFile af) {
      af.put(entry(), ":");
      auto backup = af.checkptStack();
      withTLS(namespace, this, _body.emitAsm(af));
      af.put(exit(), ":");
      af.restoreCheckptStack(backup);
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, local);
      if (!res || cast(Scope) sup)
        res = sup.lookup(name, local);
      return res;
    }
    string mangle(string name, IType type) {
      return sup.mangle(name, type) ~ "_local";
    }
    Stuple!(IType, string, int)[] stackframe() {
      auto res = fun.stackframe();
      if (auto sc = cast(Scope) sup) res ~= sc.stackframe();
      foreach (obj; field)
        if (auto var = cast(Variable) obj._1)
          res ~= stuple(var.type, var.name, var.baseOffset);
      return res;
    }
  }
}

Object gotScope(ref string text, ParseCb cont, ParseCb rest) {
  auto sc = new Scope;
  sc.sup = namespace();
  sc.fun = namespace().get!(Function);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto t2 = text;
  if (rest(t2, "tree.stmt", &sc._body)) { text = t2; return sc; }
  throw new Exception("Couldn't match scope off "~text.next_text());
}
