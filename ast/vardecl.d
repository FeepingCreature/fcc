module ast.vardecl;

import ast.assign, ast.base, ast.namespace, ast.scopes, ast.casting, ast.static_arrays, tools.base: Range;
public import ast.variable;

int vardecl_marker;

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
      initval = reinterpret_cast(
        vt,
        fastalloc!(DataExpr)(vt.initval())
      );
      initval_cache ~= stuple(initval, vt);
    }
  }
  VarDecl dup() { return fastalloc!(VarDecl)(var.dup, initval?initval.dup:null); }
  void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
    defaultIterate!(initval).iterate(dg, mode);
  }
  bool hasInitializer() {
    return !!initval;
  }
  override string getInfo() {
    return Format(dontInit?"uninitialized":"initialized"[], "; "[], marker);
  }
  override void emitLLVM(LLVMFile lf) {
    todo("VarDecl::emitLLVM");
    /*if (hasInitializer) super.emitLLVM(lf); // otherwise not worth it
    // logln("emit at "[], lf.currentStackDepth, ": "[], vars);
    // sanity checking start!
    if (var.baseOffset + var.type.size < -(lf).currentStackDepth) {
      auto delta = -(lf).currentStackDepth - (var.baseOffset + var.type.size);
      // logln("alloc "[], delta, " to compensate for stack being wrong for var "[], var.name, " @"[], var.baseOffset);
      // logln("("[], var.name, " at "[], lf.currentStackDepth, " wants "[], -var.baseOffset - var.type.size, ")"[]);
      lf.salloc(delta);
    }
    if (lf.dwarf2) {
      auto end = namespace().get!(Scope).exit();
      auto dwarf2 = lf.dwarf2;
      auto sect = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("lexical block"[]));
      string startname = qformat(".Lvardecl"[], marker);
      lf.emitLabel(startname, keepRegs, !isForward);
      sect.data ~= qformat(".long\t"[], startname);
      sect.data ~= qformat(".long\t"[], end);
      dwarf2.open(sect);
      var.registerDwarf2(dwarf2);
    }
    mixin(mustOffset("var.valueType().size()"[]));
    if (var.baseOffset + var.type.size != -(lf).currentStackDepth) {
      string name; int line;
      (fastcast!(LineNumberedStatementClass) (this)).getInfo(name, line);
      logln("Stack wrong for var emit: LOGIC ERROR; variable needs to start at "[], var.baseOffset + var.type.size, " vs. stack at "[], -(lf).currentStackDepth, ": "[], var, " at "[], name, ":"[], line);
      foreach (elem; namespace().field) {
        if (auto var = fastcast!(Variable)~ elem._1) {
          auto csd = lf.currentStackDepth;
          if (csd in
            Range[var.baseOffset .. var.baseOffset + var.type.size].endIncl)
            logln("Clobbered by "[], var, ". "[]);
        }
      }
      fail;
      // assert(false);
    }
    // sanity checking end!
    if (!hasInitializer())
      lf.salloc(var.type.size);
    else {
      int sz = var.type.size;
      mixin(mustOffset("sz"));
      // TODO: investigate why necessary for chars
      initval.emitLLVM(lf);
    }*/
  }
  override string toString() { return Format("declare [", marker, "] ", var); }
}

extern(C) int align_boffs(IType, int);

int boffs(IType t, int curdepth = -1) {
  return align_boffs(t, curdepth);
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
  todo("mkRef");
  return null;
  /*if (auto lv = fastcast!(LValue)~ ex)
    return lv;
  
  auto type = ex.valueType();
  int size = type.size;
  // void vars are fucking weird, yes.
  assert (type != Single!(Void));
  string name;
  static int x;
  synchronized name = Format("__temp_var_"[], x++, "__"[]);
  auto var = fastalloc!(Variable)(type, name,
                          boffs(type, lf.currentStackDepth));
  post = stuple(lf, lf.checkptStack()) /apply/ (LLVMFile lf, typeof(lf.checkptStack()) forble) { lf.restoreCheckptStack(forble); };
  auto vd = fastalloc!(VarDecl)(var);
  vd.initval = ex;
  vd.emitLLVM(lf);
  return var;*/
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
    return ex;
  }
  auto var = fastalloc!(Variable)(ex.valueType(), cast(string) null, boffs(ex.valueType()));
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

LValue lvize(Expr ex, Statement* late_init = null) { return ast_vardecl_lvize(ex, late_init); }

class WithTempExpr : Expr {
  OffsetExpr offs, offs_res;
  Expr thing, superthing;
  this(Expr thing, Expr delegate(Expr, OffsetExpr) dg) {
    this(thing);
    superthing = dg(offs, offs_res);
  }
  this(Expr thing) { // delayed setup. WARN: expert use only!
    offs = fastalloc!(OffsetExpr)(int.max, thing.valueType());
    offs_res = fastalloc!(OffsetExpr)(int.max, cast(IType) null);
    this.thing = thing;
  }
  // did the dg() succeed?
  bool isValid() { return !!superthing; }
  protected this() { }
  mixin defaultIterate!(thing, superthing);
  override {
    string toString() {
      return Format("<with temp "[], thing, ": "[], superthing, ">"[]);
    }
    WithTempExpr dup() {
      auto res = new WithTempExpr;
      res.offs = fastalloc!(OffsetExpr)(int.max, offs.type);
      res.offs_res = fastalloc!(OffsetExpr)(int.max, offs_res.type);
      void replace(ref Iterable it) {
        if (it is offs) it = res.offs;
        else if (it is offs_res) it = res.offs_res;
        else it.iterate(&replace);
      }
      res.thing = thing.dup;
      res.superthing = superthing.dup;
      res.superthing.iterate(&replace);
      return res;
    }
    IType valueType() { return superthing.valueType(); }
    void emitLLVM(LLVMFile lf) {
      todo("WithTempExpr::emitLLVM");
      /*auto svt = superthing.valueType();
      if (Single!(Void) == svt) {
        thing.emitLLVM(lf);
        offs.offset = -(lf).currentStackDepth;
        {
          mixin(mustOffset("0"[]));
          superthing.emitLLVM(lf);
        }
        lf.sfree(thing.valueType().size);
      } else {
        mixin(mustOffset("svt.size"[]));
        mkVar(lf, svt, true, (Variable var) {
          offs_res.offset = var.baseOffset;
          thing.emitLLVM(lf);
          offs.offset = -(lf).currentStackDepth;
          (mkAssignment(var, superthing)).emitLLVM(lf);
          lf.sfree(thing.valueType().size);
        });
      }*/
    }
  }
}

alias Expr delegate(Expr, OffsetExpr) E2EOdg; // use D calling convention!
extern(C) Expr _tmpize_maybe(Expr thing, E2EOdg dg, bool force = false);
Expr tmpize_maybe(Expr thing, Expr delegate(Expr) dg) {
  return _tmpize_maybe(thing, (Expr ex, OffsetExpr oe) { return dg(ex); });
}
Expr tmpize_maybe(Expr thing, Expr delegate(Expr, OffsetExpr) dg) {
  return _tmpize_maybe(thing, (Expr ex, OffsetExpr oe) { return dg(ex, oe); });
}
Expr tmpize(Expr thing, Expr delegate(Expr, OffsetExpr) dg) {
  return _tmpize_maybe(thing, (Expr ex, OffsetExpr oe) { return dg(ex, oe); }, true);
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
