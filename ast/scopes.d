module ast.scopes;

import ast.base, ast.namespace, ast.variable, ast.pointer, ast.casting, ast.opers, ast.literals;
import parseBase, tools.base: apply;

class Mew : LineNumberedStatementClass {
	LineNumberedStatement dup() { assert(false); }
	void iterate(void delegate(ref Iterable), IterMode mode = IterMode.Lexical) { assert(false); }
}

void fixupEBP(ref Iterable itr, Expr ebp) {
  bool needsDup, checkDup;
  void convertToDeref(ref Iterable itr) {
    // do this first so that variable initializers get fixed up
    // but not our substituted __base_ptr.
    itr.iterate(&convertToDeref, IterMode.Semantic);
    if (auto var = fastcast!(Variable) (itr)) {
      if (checkDup) needsDup = true;
      else {
        auto type = var.valueType();
        // *type*:(void*:ebp + baseOffset)
        auto nuex = new DerefExpr(
          reinterpret_cast(new Pointer(type),
            lookupOp("+",
              reinterpret_cast(voidp, ebp),
              mkInt(var.baseOffset)
            )
          )
        );
        itr = fastcast!(Iterable) (nuex);
      }
    } else if (auto r = fastcast!(Register!("ebp")) (itr)) {
      if (checkDup) needsDup = true;
      else itr = fastcast!(Iterable) (reinterpret_cast(r.valueType(), ebp));
    }
  }
  checkDup = true;
  convertToDeref(itr);
  checkDup = false;
  if (needsDup) {
    itr = itr.dup;
    convertToDeref(itr);
  }
}

import ast.aggregate, dwarf2;
class Scope : Namespace, ScopeLike, RelNamespace, LineNumberedStatement {
	Mew lnsc; // "multiple inheritance" hack
  Statement _body;
  Statement[] guards;
  int[] guard_offsets;
  ulong id;
  bool needEntryLabel;
  int pad_framesize;
  int requiredDepth; // sanity checking
  string requiredDepthDebug;
  static int scope_count;
  int count;
  mixin defaultIterate!(_body, guards);
  override void configPosition(string str) {
		lnsc.configPosition(str);
  }
  override void getInfo(ref string n, ref int l) { lnsc.getInfo(n, l); }
  Statement[] getGuards() {
    if (auto sl = fastcast!(ScopeLike) (sup)) return sl.getGuards() ~ guards;
    else return guards;
  }
  int[] getGuardOffsets() {
    if (auto sl = fastcast!(ScopeLike) (sup)) return sl.getGuardOffsets() ~ guard_offsets;
    else return guard_offsets;
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
    guard_offsets ~= namespace().get!(ScopeLike).framesize();
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
  string entry() { return Format(".L", id, "_entry"); }
  string exit() { return Format(".L", id, "_exit"); }
  string toString() { return Format("scope(", framesize(), ") <- ", sup); }
  this() {
    count = scope_count ++;
    // if (count == 3951) fail;
    id = getuid();
    sup = namespace();
    New(lnsc);
    recalcRequiredDepth;
  }
  void recalcRequiredDepth() {
    requiredDepth = framesize();
    if (requiredDepth == -1) {
      requiredDepth = int.max;
    }
    // requiredDepthDebug = Format(this);
  }
  void setSup(Namespace ns) {
    sup = ns;
    recalcRequiredDepth;
  }
  override Scope dup() {
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(sup);
    
    auto res = new Scope;
    res.field = field.dup;
    if (_body) res._body = _body.dup;
    foreach (guard; guards) res.guards ~= guard.dup;
    res.guard_offsets = guard_offsets.dup;
    res.id = getuid();
    res.lnsc = lnsc;
    res.requiredDepth = requiredDepth;
    res.requiredDepthDebug = "[dup]"~requiredDepthDebug;
    return res;
  }
  override int framesize() {
    int res;
    if (auto sl = fastcast!(ScopeLike)~ sup) {
      auto supsz = sl.framesize();
      if (supsz == -1) return -1;
      res += supsz;
    }
    foreach (obj; field) {
      if (auto var = fastcast!(Variable)~ obj._1) {
        res += getFillerFor(var.type, res);
        res += var.type.size;
      }
    }
    res += pad_framesize;
    if (isARM) {
      while (res % 4 != 0) res ++;
    }
    return res;
  }
  // frame offset caused by parameters
  int framestart() {
    return get!(FrameRoot).framestart();
  }
  bool emitted;
  // continuations good
  void delegate(bool=false) delegate() open(AsmFile af) {
    lnsc.emitAsm(af);
    // logln(lnsc.name, ":", lnsc.line, ": start(", count, ") ", this);
    if (emitted) {
      logln("double emit scope (", count, ") ", _body);
      fail;
    }
    emitted = true;
    // TODO: check for -g?
    Dwarf2Section backup_sect;
    if (af.dwarf2) {
      auto dwarf2 = af.dwarf2;
      auto sect = new Dwarf2Section(dwarf2.cache.getKeyFor("lexical block"));
      backup_sect = dwarf2.current;
      sect.data ~= qformat(".long\t", entry());
      sect.data ~= qformat(".long\t", exit());
      dwarf2.open(sect);
    }
    if (needEntryLabel || af.dwarf2) af.emitLabel(entry(), !keepRegs, !isForward);
    auto checkpt = af.checkptStack(), backup = namespace();
    namespace.set(this);
    // sanity checking
    if (requiredDepth != int.max && af.currentStackDepth != requiredDepth) {
      logln("Scope emit failure: expected stack depth ", requiredDepth, ", but got ", af.currentStackDepth);
      logln("was: ", requiredDepthDebug);
      logln(" is: ", this);
      logln("mew: ", _body);
      fail;
    }
    return stuple(checkpt, backup, this, af, backup_sect) /apply/
    (typeof(checkpt) checkpt, typeof(backup) backup, typeof(this) that, AsmFile af, Dwarf2Section backup_sect) {
      if (that._body) {
        that._body.emitAsm(af);
      }
      return stuple(checkpt, that, backup, af, backup_sect) /apply/
      (typeof(checkpt) checkpt, typeof(that) that, typeof(backup) backup, AsmFile af, Dwarf2Section backup_sect, bool onlyCleanup) {
        if (!onlyCleanup) {
          if (af.dwarf2) {
            af.markLabelInUse(that.exit());
          }
          af.emitLabel(that.exit(), !keepRegs, isForward);
          if (af.dwarf2) {
            af.dwarf2.closeUntil(backup_sect);
          }
        }
        
        foreach_reverse(i, guard; that.guards) {
          af.restoreCheckptStack(that.guard_offsets[i]);
          guard.emitAsm(af);
        }
        
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
    Object lookupRel(string name, Expr base, bool isDirectLookup = true) {
      auto res = lookup(name, false);
      if (!res) return null;
      auto r2 = fastcast!(Namespace) (get!(IModule)).lookup(name, false);
      if (r2 is res) return null; // nonlocal
      auto itr = fastcast!(Iterable) (res);
      fixupEBP(itr, base);
      return fastcast!(Object) (itr);
    }
    bool isTempNamespace() { return false; }
    string mangle(string name, IType type) {
      // fail;
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

// gotScope moved to fcc.d
