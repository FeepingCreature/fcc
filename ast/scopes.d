module ast.scopes;

import ast.base, ast.namespace, ast.fun, ast.variable, parseBase;

class Scope : Namespace, Tree {
  Function fun;
  Statement _body;
  ulong id;
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
  Stuple!(Type, string, int)[] members() {
    Stuple!(Type, string, int)[] res;
    if (auto sc = cast(Scope) sup)
      res = sc.members();
    foreach (obj; field)
      if (auto var = cast(Variable) obj._1)
        res ~= stuple(var.type, var.name, var.baseOffset);
    return res;
  }
  override {
    void emitAsm(AsmFile af) {
      af.put(entry(), ":");
      auto backup = af.checkptStack();
      withTLS(namespace, this, _body.emitAsm(af));
      af.put(exit(), ":");
      af.restoreCheckptStack(backup);
    }
    string mangle(string name, Type type) {
      return sup.mangle(name, type) ~ "_local";
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
