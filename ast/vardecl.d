module ast.vardecl;

import ast.assign, ast.base, ast.namespace, ast.scopes, ast.casting, ast.static_arrays, tools.base: Range;
public import ast.variable;

int vardecl_marker, anonvar;

string getAnonvarId() { synchronized return qformat("anon_var_", anonvar ++); }

import dwarf2;
class VarDecl : LineNumberedStatementClass, HasInfo {
  Variable var;
  int marker;
  Expr initval;
  bool dontInit;
  this(Variable v, Expr initval = null) {
    var = v;
    if (Single!(Void) == v.type) {
      logln("tried to declare void variable"[]);
      fail;
    }
    marker = .vardecl_marker ++;
    // if (marker == 10578) { logln(this); asm { int 3; } }
    if (!initval) {
      /*
      if (marker == 12) { logln(this); asm { int 3; } }
      if (xpar == -1 || marker < xpar) dontInit = true;
      else initInit();*/
      dontInit = true;
    } else this.initval = initval;
  }
  static Stuple!(Expr, IType)[] initval_cache;
  void initInit() {
    // if (initval) fail("initval already present");
    if (initval) return;
    dontInit = false;
    auto vt = var.valueType();
    synchronized {
      foreach (ref entry; initval_cache)
        if (entry._1 == vt) {
          initval = entry._0;
          return;
        }
      initval = fastalloc!(ZeroInitializer)(vt);
      initval_cache ~= stuple(initval, vt);
    }
  }
  VarDecl dup() { return fastalloc!(VarDecl)(var.dup, initval?initval.dup:null); }
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    defaultIterate!(initval).iterate(dg, mode);
  }
  mixin defaultCollapse!();
  bool hasInitializer() {
    return !!initval;
  }
  override string getInfo() {
    return Format(dontInit?"uninitialized":"initialized"[], "; "[], marker);
  }
  override void emitLLVM(LLVMFile lf) {
    if (hasInitializer) {
      super.emitLLVM(lf);
      emitAssign(lf, var, initval);
    }
  }
  override string toString() { return Format("declare [", marker, "] ", var); }
}

void mkVar(LLVMFile lf, IType type, bool dontInit, bool alignvar, void delegate(Variable) dg) {
  todo("mkVar");
  // void vars are fucking weird.
  /*if (Single!(Void) == type) { dg(null); return; }
  int size = type.size;
  mixin(mustOffset("size"[]));
  string name;
  static int x;
  synchronized name = Format("__temp_res_var_"[], x++, "__"[]);
  auto bof = boffs(type, lf.currentStackDepth), naturalOffs = -(lf.currentStackDepth + type.size);
  bool needsAlignment = bof != naturalOffs;
  if (alignvar && needsAlignment) { // write into temporary
    mkVarUnaligned(lf, type, true, (Variable var) {
      auto delta = -(lf.currentStackDepth + type.size) - boffs(type, lf.currentStackDepth);
      lf.salloc(delta);
      assert(!-(lf.currentStackDepth + type.size) - boffs(type, lf.currentStackDepth)); // copypaste yay
      mkVar(lf, type, true, (Variable var2) {
        dg(var2);
        (mkAssignment(var, var2)).emitLLVM(lf);
      });
      lf.sfree(type.size);
      lf.sfree(delta);
    });
  } else {
    auto var = fastalloc!(Variable)(type, name,
                            alignvar?bof:naturalOffs);
    if (size) {
      mixin(mustOffset("size"[], "2"[]));
      auto vd = fastalloc!(VarDecl)(var);
      if (dontInit) vd.dontInit = true;
      else vd.initInit;
      vd.emitLLVM(lf);
    }
    {
      mixin(mustOffset("0"[]));
      dg(var);
    }
  }*/
}

void mkVar(LLVMFile lf, IType type, bool dontInit, void delegate(Variable) dg) {
  mkVar(lf, type, dontInit, true, dg);
}

void mkVarUnaligned(LLVMFile lf, IType type, bool dontInit, void delegate(Variable) dg) {
  mkVar(lf, type, dontInit, false, dg);
}

import tools.base;
LValue mkRef(LLVMFile lf, Expr ex, ref void delegate() post) {
  if (auto lv = fastcast!(LValue)~ ex)
    return lv;
  
  auto lr = fastalloc!(LLVMRef)(ex.valueType());
  lr.allocate(lf);
  lr.begin(lf);
  emitAssign(lf, lr, ex);
  return lr;
}

Expr tmpize_if_possible(Expr ex, Statement* late_init = null) {
  if (auto var = fastcast!(Variable) (ex)) return ex;
  /*if (late_init) if (auto sal = fastcast!(StatementAndLValue) (ex)) {
    if (auto var = fastcast!(Variable) (sal.second)) {
      *late_init = sal.first;
      return sal.second;
    }
  }*/
  auto sc = namespace().get!(Scope);
  if (!sc) {
    // logln("oh look the weird thing happened :D while tmpizing ", ex, " in ", namespace());
    // fail;
    return ex;
  }
  auto var = fastalloc!(Variable)(ex.valueType(), framelength(), cast(string) null);
  // TODO: is it really valid to add to a scope beneath a nested namespace?
  // Won't this mess up the frame size counts? .. Meh.
  // NOTE: THIS IS VERY VERY VEEEEERRY IFFY
  // because it changes the semantics; specifically, the evaluation point of ex() to the variable declaration point
  // only use lvize() if you are aware of this!
  // NOTE: for this reason, late_init was added
  
  auto decl = fastalloc!(VarDecl)(var);
  if (late_init) {
    *late_init = fastalloc!(Assignment)(var, ex);
    decl.dontInit = true;
  } else {
    decl.initval = ex;
  }
  sc.addStatement(decl);
  sc.add(var);
  return var;
}

// create temporary if needed
extern(C) LValue ast_vardecl_lvize(Expr ex, Statement* late_init = null) {
  if (auto lv = fastcast!(LValue) (ex)) return lv;
  if (!namespace().get!(Scope)) {
    logln("No Scope beneath "[], namespace(), " for lvizing "[], ex, "!"[]);
    fail;
  }
  return fastcast!(LValue) (tmpize_if_possible(ex, late_init));
}

class WithTempExpr : Expr {
  LLVMValue val; LLVMRef lltemp;
  Expr thing, superthing;
  this(Expr thing, Expr delegate(Expr, LLVMRef) dg) {
    this(thing);
    superthing = dg(val, lltemp);
  }
  this(Expr thing) { // delayed setup. WARN: expert use only!
    val = fastalloc!(LLVMValue)(cast(string) null, thing.valueType());
    lltemp = fastalloc!(LLVMRef)();
    this.thing = thing;
  }
  this() { }
  void copy(WithTempExpr wte) {
    val        = wte.val;
    lltemp     = wte.lltemp;
    thing      = wte.thing;
    superthing = wte.superthing;
  }
  // did the dg() succeed?
  bool isValid() { return !!superthing; }
  mixin defaultIterate!(thing, superthing);
  mixin defaultCollapse!();
  WithTempExpr create() { return fastalloc!(WithTempExpr)(); }
  override {
    string toString() {
      return Format("<with temp "[], thing, ": "[], superthing, ">"[]);
    }
    Expr dup() {
      auto res = create();
      res.val = fastalloc!(LLVMValue)(cast(string) null, val.type);
      res.lltemp = fastalloc!(LLVMRef)();
      if (lltemp.type) res.lltemp.type = lltemp.type;
      void replace(ref Iterable it) {
        if (it is val) it = res.val;
        else if (it is lltemp) it = res.lltemp;
        else it.iterate(&replace);
      }
      res.thing = thing.dup;
      res.superthing = superthing.dup;
      res.superthing.iterate(&replace);
      return res;
    }
    IType valueType() { return superthing.valueType(); }
    void emitLLVM(LLVMFile lf) {
      mixin(mustOffset("1"));
      val.str = save(lf, thing);
      // logln("set val(", val.count, ") str to '", val.str, "'");
      if (lltemp.type) {
        lltemp.allocate(lf);
        lltemp.begin(lf);
      }
      superthing.emitLLVM(lf);
      if (lltemp.type) {
        lltemp.end(lf);
      }
    }
  }
}

class WithTempMValue : WithTempExpr, MValue {
  bool alreadyUsed;
  this(Expr thing) { super(thing); }
  this() { }
  override {
    MValue dup() { return fastcast!(MValue)(super.dup()); } // type works out due to create()
    WithTempExpr create() { return fastalloc!(WithTempMValue)(); }
    string toString() { return Format("<with temp (mvalue) "[], thing, ": "[], superthing, ">"[]); }
    void emitLLVM(LLVMFile lf) {
      if (alreadyUsed) fail; alreadyUsed = true;
      super.emitLLVM(lf);
    }
    void emitAssignment(LLVMFile lf) {
      if (alreadyUsed) fail; alreadyUsed = true;
      auto supermv = fastcast!(MValue)(superthing);
      if (!supermv) fail;
      val.str = save(lf, thing);
      if (lltemp.type) {
        lltemp.allocate(lf);
        lltemp.begin(lf);
      }
      supermv.emitAssignment(lf);
      if (lltemp.type) {
        lltemp.end(lf);
      }
    }
  }
}

LValue lvize(Expr ex, Statement* late_init = null) { return ast_vardecl_lvize(ex, late_init); }

alias Expr delegate(Expr, LLVMRef) E2ERdg; // use D calling convention!
extern(C) Expr _tmpize_maybe(Expr thing, E2ERdg dg, bool force = false);
Expr tmpize_maybe(Expr thing, Expr delegate(Expr) dg) {
  return _tmpize_maybe(thing, (Expr ex, LLVMRef llr) { return dg(ex); });
}
Expr tmpize_maybe(Expr thing, Expr delegate(Expr, LLVMRef) dg) {
  return _tmpize_maybe(thing, (Expr ex, LLVMRef llr) { return dg(ex, llr); });
}
Expr tmpize(Expr thing, Expr delegate(Expr, LLVMRef) dg) {
  return _tmpize_maybe(thing, (Expr ex, LLVMRef llr) { return dg(ex, llr); }, true);
}

import ast.pointer;
Expr tmpize_ref_maybe(Expr thing, Expr delegate(Expr) dg) {
  if (auto lv = fastcast!(LValue) (thing)) {
    return tmpize_maybe(new RefExpr(lv), delegate Expr(Expr ex) { return dg(new DerefExpr(ex)); });
  }
  return tmpize_maybe(thing, dg);
}

import ast.fold;
Expr mkTemp(LLVMFile lf, Expr ex, ref void delegate() post) {
  if (fastcast!(Literal) (ex)) return ex;
  return mkRef(lf, ex, post);
}
