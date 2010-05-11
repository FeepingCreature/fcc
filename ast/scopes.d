module ast.scopes;

import ast.base, ast.namespace, ast.fun;

class Scope : Namespace, Tree {
  Function fun;
  Statement _body;
  ulong id;
  string entry() { return Format(fun.mangleSelf(), "_entry", id); }
  string exit() { return Format(fun.mangleSelf(), "_exit", id); }
  string toString() { return Format("scope <- ", sup); }
  this() { id = getuid(); }
  int framesize() {
    // TODO: alignment
    int res;
    foreach (var; Varfield) {
      res += var._1.type.size;
    }
    if (auto sc = cast(Scope) sup)
      res += sc.framesize();
    return res;
  }
  override {
    void emitAsm(AsmFile af) {
      af.put(entry(), ":");
      auto backup = af.checkptStack();
      _body.emitAsm(af);
      af.put(exit(), ":");
      af.restoreCheckptStack(backup);
    }
    string mangle(string name, Type type) {
      return sup.mangle(name, type) ~ "_local";
    }
  }
}

Function findFun(Namespace ns) {
  if (auto res = cast(Function) ns) return res;
  else return findFun(ns.sup);
}
