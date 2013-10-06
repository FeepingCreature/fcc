module ast.scopes;

import ast.base, ast.namespace, ast.variable, ast.pointer, ast.casting, ast.opers, ast.literals;
import parseBase, tools.base: apply;

class Mew : LineNumberedStatementClass {
  LineNumberedStatement dup() { assert(false); }
  void iterate(void delegate(ref Iterable), IterMode mode = IterMode.Lexical) { assert(false); }
  Tree collapse() { assert(false); }
}

class SuperContextAccess : LValue {
  Expr baseptr;
  IType valuetype;
  string type;
  int index;
  this(Expr bp, IType vt, string t, int i) {
    this.baseptr = bp;
    this.valuetype = vt;
    this.type = t;
    this.index = i;
  }
  mixin defaultIterate!(baseptr);
  mixin defaultCollapse!();
  override {
    string toString() { return qformat("[", valuetype, " @", index, "](", /*type, " ", */baseptr, ")"); }
    SuperContextAccess dup() {
      return fastalloc!(SuperContextAccess)(baseptr.dup, valuetype, type, index); 
    }
    IType valueType() { return valuetype; }
    void emitLLVM(LLVMFile lf) {
      emitLocation(lf);
      load(lf, "load ", typeToLLVM(valuetype), "* ", lf.pop());
    }
    void emitLocation(LLVMFile lf) {
      auto bs = save(lf, baseptr);
      llcast(lf, typeToLLVM(baseptr.valueType()), type ~ "*", bs);
      load(lf, "getelementptr  inbounds ", type, "* ", lf.pop(), ", i32 0, i32 ", index);
    }
  }
}

void fixupEBP(ref Iterable itr, Expr baseptr) {
  auto outer_itr = itr;
  bool needsDup, checkDup;
  void convertToDeref(ref Iterable itr) {
    // do this first so that variable initializers get fixed up
    // but not our substituted __base_ptr.
    itr.iterate(&convertToDeref, IterMode.Semantic);
    if (auto var = fastcast!(Variable) (itr)) {
      if (checkDup) needsDup = true;
      else {
        auto type = var.valueType();
        auto nuex = fastalloc!(SuperContextAccess)(baseptr, type, var.stacktype, var.baseIndex);
        itr = fastcast!(Iterable)(nuex);
        /*auto type = var.valueType();
        // *type*:(void*:ebp + baseOffset)
        auto nuex = fastalloc!(DerefExpr)(
          reinterpret_cast(fastalloc!(Pointer)(type),
            lookupOp("+"[],
              reinterpret_cast(voidp, ebp),
              mkInt(var.baseOffset)
            )
          )
        );
        itr = fastcast!(Iterable) (nuex);*/
      }
    } else if (auto r = fastcast!(Register!("ebp"[])) (itr)) {
      // will be replaced with our new stackptr, so it's okay
      // logln("wat (confused by ebp in ", outer_itr, ")");
      // fail;
      if (checkDup) needsDup = true;
      else itr = fastcast!(Iterable) (reinterpret_cast(r.valueType(), baseptr));
    }
  }
  checkDup = true;
  convertToDeref(itr);
  checkDup = false;
  if (needsDup) {
    // logln("FIXUP: before ", itr);
    itr = itr.dup;
    convertToDeref(itr);
    // logln("FIXUP: after ", itr);
  }
}

extern(C) void recordFrame(Scope sc);

import ast.aggregate, dwarf2;
class Scope : Namespace, ScopeLike, RelNamespace, LineNumberedStatement {
	Mew lnsc; // "multiple inheritance" hack
  Statement _body;
  Statement[] guards;
  int[] guard_offsets;
  ulong id;
  bool needEntryLabel;
  static int scope_count;
  int count;
  // mixin defaultIterate!(_body, guards);
  override void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    defaultIterate!(_body, guards).iterate(dg, mode);
  }
  mixin defaultCollapse!();
  override void configPosition(string str) {
		lnsc.configPosition(str);
  }
  override void getInfo(ref string n, ref int l, ref int c) { lnsc.getInfo(n, l, c); }
  Statement[] getGuards() {
    if (auto sl = fastcast!(ScopeLike) (sup)) return sl.getGuards() ~ guards;
    else return guards;
  }
  int[] getGuardOffsets() {
    if (auto sl = fastcast!(ScopeLike) (sup)) return sl.getGuardOffsets() ~ guard_offsets;
    else return guard_offsets;
  }
  void addStatement(Statement st) {
    if (auto as = fastcast!(AggrStatement)(_body)) as.stmts ~= st;
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
  string entry() { return Format(".L"[], id, "_entry"[]); }
  string exit() { return Format(".L"[], id, "_exit"[]); }
  bool tostringing;
  string toString() {
    if (tostringing) return Format("scope(", framelength2(this), " ", count, ")");
    tostringing = true;
    scope(exit) tostringing = false;
    return Format("scope(", framelength2(this), " ", count, " ", field, ") <- ", sup);
  }
  this() {
    count = scope_count ++;
    // if (count == 5902) asm { int 3; }
    id = getuid();
    sup = namespace();
    lnsc = fastalloc!(Mew)();
  }
  void setSup(Namespace ns) {
    sup = ns;
  }
  override Scope dup() {
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    
    auto res = new Scope;
    res.field = field.dup;
    
    namespace.set(res);
    if (_body) res._body = _body.dup;
    foreach (guard; guards) res.guards ~= guard.dup;
    res.guard_offsets = guard_offsets.dup;
    res.id = getuid();
    res.lnsc = lnsc;
    return res;
  }
  bool emitted;
  // assume the same scope won't be opened twice
  Namespace active_backup_ns;
  LLVMFile active_lf;
  Dwarf2Section active_backup_sect;
  void open3(bool onlyCleanup) {
    auto lf = active_lf;
    if (!onlyCleanup) {
      /*if (lf.dwarf2) {
        lf.markLabelInUse(exit());
      }*/
      lf.emitLabel(exit(), true);
      /*if (lf.dwarf2) {
        lf.dwarf2.closeUntil(active_backup_sect);
      }*/
    }
    foreach_reverse(i, guard; guards) {
      guard.emitLLVM(lf);
    }
    // logln("record ", this);
    // logln("having been ", _body);
    // logln("guards ", guards);
    recordFrame(this);
    if (!onlyCleanup) namespace.set(active_backup_ns);
  }
  void delegate(bool onlyCleanup) open2() {
    if (_body) {
      _body.emitLLVM(active_lf);
    }
    return &open3;
  }
  // continuations good
  void delegate(bool onlyCleanup) delegate() open(LLVMFile lf) {
    // lnsc.emitLLVM(lf);
    // logln(lnsc.name, ":"[], lnsc.line, ": start("[], count, "[]) "[], this);
    if (emitted) {
      logln("double emit scope ("[], count, "[]) "[], _body);
      fail;
    }
    emitted = true;
    // TODO: check for -g?
    /*Dwarf2Section backup_sect;
    if (lf.dwarf2) {
      auto dwarf2 = lf.dwarf2;
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("lexical block"[]));
      backup_sect = dwarf2.current;
      sect.data ~= qformat(".long\t"[], entry());
      sect.data ~= qformat(".long\t"[], exit());
      dwarf2.open(sect);
    }*/
    // if (needEntryLabel || lf.dwarf2) lf.emitLabel(entry(), !keepRegs, !isForward);
    if (needEntryLabel) lf.emitLabel(entry());
    auto backup = namespace();
    namespace.set(this);
    // sanity checking
    active_backup_ns = backup;
    active_lf = lf;
    // active_backup_sect = backup_sect;
    return &open2;
  }
  override {
    void emitLLVM(LLVMFile lf) {
      open(lf)()(false); // lol
    }
    Object lookup(string name, bool local = false) {
      bool pointless;
      if (name.find(".") != -1) pointless = true; // only modules match this
      Object res;
      if (!pointless) res = super.lookup(name, true);
      if (res) return res;
      return sup.lookup(name, local);
    }
    Object lookupRel(string name, Expr base, bool isDirectLookup = true) {
      auto res = lookup(name, false);
      if (!res) return null;
      // look for possible import
      Namespace test = this;
      while (test && test.sup) {
        auto imp = test.sup.get!(Importer);
        if (!imp) break;
        auto above = imp.lookupInImports(name, false);
        if (above is res) return null; // nonlocal
        test = fastcast!(Namespace)(imp);
      }
      auto itr = fastcast!(Iterable) (res);
      if (!itr) { logln("weird-ass: ", res, " but not iterable - ", isDirectLookup); fail; }
      fixupEBP(itr, base);
      return fastcast!(Object) (itr);
    }
    bool isTempNamespace() { return false; }
    string mangle(string name, IType type) {
      // fail;
      return sup.mangle(name, type) ~ "_local";
    }
    Stuple!(IType, string)[] stackframe() {
      Stuple!(IType, string)[] res;
      if (sup) res = sup.get!(ScopeLike).stackframe();
      foreach (obj; field)
        if (auto var = fastcast!(Variable)~ obj._1)
          res ~= stuple(var.type, var.name);
      return res;
    }
  }
}

// gotScope moved to fcc.d
