module ast.scopes;

import ast.base, ast.namespace, ast.fun, ast.variable, parseBase, tools.base: apply;

interface ScopeLike {
  int framesize();
}

class Scope : Namespace, Tree, ScopeLike {
  Function fun;
  Statement _body;
  Statement[] guards;
  ulong id;
  mixin defaultIterate!(_body, guards);
  Statement[] getGuards() {
    if (auto sc = cast(Scope) sup) return sc.getGuards() ~ guards;
    else return guards;
  }
  string entry() { return Format(fun.mangleSelf(), "_entry", id); }
  string exit() { return Format(fun.mangleSelf(), "_exit", id); }
  string toString() { return Format("scope <- ", sup); }
  this() { id = getuid(); }
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
    return fun.framestart();
  }
  // continuations good
  void delegate() delegate() open(AsmFile af) {
    af.put(entry(), ":");
    auto checkpt = af.checkptStack(), backup = namespace();
    namespace.set(this);
    return stuple(checkpt, backup, this, af) /apply/ (typeof(checkpt) checkpt, typeof(backup) backup, typeof(this) that, AsmFile af) {
      that._body.emitAsm(af);
      return stuple(checkpt, that, backup, af) /apply/ (typeof(checkpt) checkpt, typeof(that) that, typeof(backup) backup, AsmFile af) {
        af.put(that.exit(), ":");
        
        foreach_reverse(guard; that.guards)
          guard.emitAsm(af);
        
        af.restoreCheckptStack(checkpt);
        namespace.set(backup);
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
      if (!res && cast(Scope) sup)
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
mixin DefaultParser!(gotScope, "tree.scope");
