module ast.pointer;

import ast.types, ast.base, parseBase, tools.base: This, This_fn, rmSpace;

import dwarf2;
class Pointer_ : Type, Dwarf2Encodable {
  IType target;
  this(IType t) { target = forcedConvert(t); }
  override {
    int opEquals(IType ty) {
      ty = resolveType(ty);
      if (!super.opEquals(ty)) return false;
      auto p = fastcast!(Pointer)~ ty;
      return target == p.target;
    }
    int size() { return nativePtrSize; }
    string mangle() { return "ptrto_"~target.mangle(); }
    string toString() { return Format(target, "*"); }
    bool canEncode() {
      auto d2e = fastcast!(Dwarf2Encodable)(resolveType(target));
      return d2e && d2e.canEncode();
    }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      auto targetref = registerType(dwarf2, fastcast!(Dwarf2Encodable) (resolveType(target)));
      auto targetpsec = new Dwarf2Section(dwarf2.cache.getKeyFor("pointer type"));
      with (targetpsec) {
        data ~= targetref;
        data ~= ".4byte\t4\t/* pointer size */";
      }
      return targetpsec;
    }
  }
}

final class Pointer : Pointer_ {
  this(IType t) { super(t); }
}

alias Single!(Pointer, Single!(Void)) voidp;

// &foo
class RefExpr : Expr {
  CValue src;
  int counter;
  static int pointer_counter;
  this(CValue cv) { if (!cv) fail; this.src = cv; this(); }
  private this() {
    counter = pointer_counter ++;
    // if (counter == 5101) fail;
  }
  mixin DefaultDup!();
  mixin defaultIterate!(src);
  override {
    IType valueType() {
      return new Pointer(src.valueType());
    }
    void emitAsm(AsmFile af) {
      src.emitLocation(af);
    }
    string toString() {
      return Format("&", src);
    }
  }
}

// *foo
class DerefExpr : LValue, HasInfo {
  Expr src;
  int count;
  static int de_count;
  this(Expr ex) {
    this();
    src = ex;
    if (!fastcast!(Pointer) (resolveType(src.valueType())))
      throw new Exception(Format("Can't dereference non-pointer: ", src));
  }
  private this() { count = de_count ++; }
  mixin DefaultDup!();
  mixin defaultIterate!(src);
  override {
    string getInfo() { return Format("count: ", count); }
    IType valueType() {
      return fastcast!(Pointer) (resolveType(src.valueType())).target;
    }
    void emitAsm(AsmFile af) {
      int sz = valueType().size;
      mixin(mustOffset("sz"));
      if (isARM && sz == 1) {
        af.salloc(1);
        src.emitAsm(af);
        af.popStack("r2", 4);
        af.mmove1("[r2]", "r2");
        af.mmove1("r2", "[sp]");
        return;
      }
      src.emitAsm(af);
      if (isARM) {
        af.popStack("r2", nativePtrSize);
        armpush(af, "r2", sz);
      } else {
        af.popStack("%edx", nativePtrSize);
        af.pushStack("(%edx)", sz);
        af.nvm("%edx");
      }
    }
    void emitLocation(AsmFile af) {
      src.emitAsm(af);
    }
  }
  string toString() { return Format("*", src); }
}

bool isVoidP(IType it) {
  if (!it) return false;
  auto p = fastcast!(Pointer)~ it;
  if (!p) return false;
  return !!fastcast!(Void) (p.target);
}

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    if (text.accept("*")) { return new Pointer(cur); }
    else return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto re = fastcast!(RefExpr) (it)) {
      if (auto de = fastcast!(DerefExpr) (re.src)) {
        return fastcast!(Itr) (de.src);
      }
    }
    return null;
  };
  // Pointers must NOT autocast to void* unless expected!
  implicits ~= delegate Expr(Expr ex, IType target) {
    if (!target) return null;
    if (auto p = fastcast!(Pointer) (resolveType(ex.valueType()))) {
      if (!isVoidP(p) && isVoidP(target)) {
        return dcm(reinterpret_cast(voidp, ex));
      }
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex, IType expect) {
    if (isVoidP(ex.valueType()) && fastcast!(Pointer) (resolveType(expect))) {
      return reinterpret_cast(expect, ex);
    }
    return null;
  };
}

import ast.fold, ast.casting;
Object gotRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex)) {
    text.setError("Address operator found but nothing to take address matched");
    return null;
  }
  
  IType[] tried;
  if (!gotImplicitCast(ex, (Expr ex) {
    auto f = foldex(forcedConvert(ex));
    unrollSAE(f);
    tried ~= f.valueType();
    return test(fastcast!(CValue)~ f);
  })) {
    // text.setError("Can't take reference: ", ex,
    // " does not become a cvalue (", tried, ")");
    text.setError("Can't take reference: expression does not seem to have an address");
    return null;
  }
  
  text = t2;
  auto thing = foldex(forcedConvert(ex));
  Statement st;
  if (auto _st = unrollSAE(thing)) st = _st;
  auto cv = fastcast!(CValue) (thing);
  assert(!!cv);
  
  Expr res = new RefExpr(cv);
  if (st) res = mkStatementAndExpr(st, res);
  return fastcast!(Object) (res);
}
mixin DefaultParser!(gotRefExpr, "tree.expr.ref", "21", "&");

Object gotDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    t2.failparse("Dereference operator found but no expression matched");
  
  if (!gotImplicitCast(ex, (IType it) { return !!fastcast!(Pointer) (it); })) {
    return null;
  }
  text = t2;
  return new DerefExpr(ex);
}
mixin DefaultParser!(gotDerefExpr, "tree.expr.deref", "22", "*");

class Symbol : Expr {
  string _name;
  string getName() { return _name; }
  this(string name) { this._name = name; }
  this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override IType valueType() { return voidp; }
  override void emitAsm(AsmFile af) {
    if (isARM) {
      af.mmove4("="~getName(), "r0");
      // af.pool;
      af.pushStack("r0", 4);
    } else {
      af.pushStack("$"~getName(), nativePtrSize);
    }
  }
}

// fill string at emitAsm-time via dg
class LateSymbol : Expr {
  void delegate(AsmFile) dg;
  string* name;
  this(void delegate(AsmFile) dg, string* name) { this.dg = dg; this.name = name; }
  private this() { }
  LateSymbol dup() { return new LateSymbol(dg, name); }
  mixin defaultIterate!();
  override IType valueType() { return voidp; }
  override void emitAsm(AsmFile af) {
    if (!*name) dg(af);
    if (isARM) {
      af.mmove4("="~*name, "r0");
      af.pushStack("r0", 4);
    } else {
      af.pushStack("$"~*name, nativePtrSize);
    }
  }
}
