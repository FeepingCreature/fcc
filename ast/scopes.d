module ast.scopes;

import ast.base, ast.namespace, ast.variable, parseBase, tools.base: apply;

class Mew : LineNumberedStatementClass {
	LineNumberedStatement dup() { assert(false); }
	void iterate(void delegate(ref Iterable)) { assert(false); }
}

import ast.aggregate;
class Scope : Namespace, ScopeLike, LineNumberedStatement {
	Mew lnsc; // "multiple inheritance" hack
  Statement _body;
  Statement[] guards;
  ulong id;
  mixin defaultIterate!(_body, guards);
  override void configPosition(string str) {
		lnsc.configPosition(str);
  }
  override void getInfo(ref string n, ref int l) { lnsc.getInfo(n, l); }
  Statement[] getGuards() {
    if (auto sc = fastcast!(Scope)~ sup) return sc.getGuards() ~ guards;
    else return guards;
  }
  void addStatement(Statement st) {
    if (auto as = fastcast!(AggrStatement) (_body)) as.stmts ~= st;
    else if (!_body) _body = st;
    else {
      auto as = new AggrStatement;
      as.stmts ~= _body;
      as.stmts ~= st;
      _body = as;
    }
  }
  void addGuard(Statement st) {
    guards ~= st;
  }
  void addStatementToFront(Statement st) {
    if (auto as = fastcast!(AggrStatement) (_body)) as.stmts = st ~ as.stmts;
    else if (!_body) _body = st;
    else {
      auto as = new AggrStatement;
      as.stmts ~= st;
      as.stmts ~= _body;
      _body = as;
    }
  }
  // string entry() { return Format(base, "_entry", id); }
  // string exit() { return Format(base, "_exit", id); }
  string entry() { return Format(".L", id, "_entry"); }
  string exit() { return Format(".L", id, "_exit"); }
  string toString() { /*return Format(_body);*/ return Format("scope <- ", sup); }
  this() {
    id = getuid();
    sup = namespace();
    New(lnsc);
  }
  override Scope dup() {
    auto res = new Scope;
    res.field = field.dup;
    if (_body) res._body = _body.dup;
    foreach (guard; guards) res.guards ~= guard.dup;
    res.id = getuid();
    res.lnsc = lnsc;
    return res;
  }
  override int framesize() {
    int res;
    if (auto sl = fastcast!(ScopeLike)~ sup)
      res += sl.framesize();
    foreach (obj; field) {
      if (auto var = fastcast!(Variable)~ obj._1) {
        res += getFillerFor(var.type, res);
        res += var.type.size;
      }
    }
    return res;
  }
  // frame offset caused by parameters
  int framestart() {
    return get!(FrameRoot).framestart();
  }
  // continuations good
  bool emitted;
  void delegate(bool=false) delegate() open(AsmFile af) {
		lnsc.emitAsm(af);
		// logln(lnsc.name, ":", lnsc.line, ": start ", this);
		if (emitted) {
			logln("double emit scope. ");
			asm { int 3; }
		}
		emitted = true;
    af.emitLabel(entry());
    auto checkpt = af.checkptStack(), backup = namespace();
    namespace.set(this);
    return stuple(checkpt, backup, this, af) /apply/ (typeof(checkpt) checkpt, typeof(backup) backup, typeof(this) that, AsmFile af) {
      if (that._body) {
        that._body.emitAsm(af);
      }
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
      auto res = super.lookup(name, true);
      // TODO: &&? ||? WHO KNOWS =D
      // if (!res && fastcast!(Scope)~ sup)
      if (res) return res;
      return sup.lookup(name, local);
    }
    string mangle(string name, IType type) {
      // asm { int 3; }
      return sup.mangle(name, type) ~ "_local";
    }
    Stuple!(IType, string, int)[] stackframe() {
      typeof(sup.stackframe()) res;
      if (sup) res = sup.stackframe();
      foreach (obj; field)
        if (auto var = fastcast!(Variable)~ obj._1)
          res ~= stuple(var.type, var.name, var.baseOffset);
      return res;
    }
  }
  int frame_end() { int res; foreach (entry; stackframe()) { res = min(res, entry._2); } return res; }
}

Object gotScope(ref string text, ParseCb cont, ParseCb rest) {
  if (auto res = rest(text, "tree.stmt.aggregate")) return res; // always scope anyway
  auto sc = new Scope;
  sc.configPosition(text);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto t2 = text;
  if (rest(t2, "tree.stmt", &sc._body)) { text = t2; return sc; }
  t2.failparse("Couldn't match scope");
}
mixin DefaultParser!(gotScope, "tree.scope");
