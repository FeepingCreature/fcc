module ast.vardecl;

import ast.assign, ast.base, tools.base: Range;
public import ast.variable;

import ast.pointer, ast.casting;
class VarDecl : LineNumberedStatementClass {
  Variable var;
  this(Variable v) {
    var = v;
    if (v.valueType() == Single!(Void)) {
      logln("tried to declare void variable");
      fail;
    }
  }
  VarDecl dup() { return new VarDecl(var.dup); }
  mixin defaultIterate!(var);
  bool hasInitializer() {
    return !var.dontInit;
  }
  override void emitAsm(AsmFile af) {
    if (hasInitializer) super.emitAsm(af); // otherwise not worth it
    // logln("emit at ", af.currentStackDepth, ": ", vars);
    // sanity checking start!
    if (var.baseOffset + var.type.size < -af.currentStackDepth) {
      auto delta = -af.currentStackDepth - (var.baseOffset + var.type.size);
      // logln("alloc ", delta, " to compensate for stack being wrong for var ", var.name, " @", var.baseOffset);
      // logln("(", var.name, " at ", af.currentStackDepth, " wants ", -var.baseOffset - var.type.size, ")");
      af.salloc(delta);
    }
    mixin(mustOffset("var.valueType().size()"));
    if (var.baseOffset + var.type.size != -af.currentStackDepth) {
      logln("Stack wrong for var emit: LOGIC ERROR; variable needs to start at ", var.baseOffset + var.type.size, " vs. stack at ", -af.currentStackDepth, ": ", var);
      foreach (elem; namespace().field) {
        if (auto var = fastcast!(Variable)~ elem._1) {
          auto csd = af.currentStackDepth;
          if (csd in
            Range[var.baseOffset .. var.baseOffset + var.type.size].endIncl)
            logln("Clobbered by ", var, ". ");
        }
      }
      fail;
      // assert(false);
    }
    // sanity checking end!
    if (var.dontInit)
      af.salloc(var.type.size);
    else {
      if (var.type == Single!(Void)) {
        mixin(mustOffset("0"));
        if (var.initval) var.initval.emitAsm(af);
        return;
      }
      mixin(mustOffset("var.type.size"));
      int sz = var.type.size;
      // TODO: investigate why necessary for chars
      var.initval.emitAsm(af);
    }
  }
  override string toString() { return Format("declare ", var); }
}

extern(C) int align_boffs(IType, int);

int boffs(IType t, int curdepth = -1) {
  return align_boffs(t, curdepth);
}

void mkVar(AsmFile af, IType type, bool dontInit, bool alignvar, void delegate(Variable) dg) {
  int size = type.size;
  // void vars are fucking weird.
  if (type == Single!(Void)) size = 0;
  mixin(mustOffset("size"));
  string name;
  static int x;
  synchronized name = Format("__temp_res_var_", x++, "__");
  auto var = new Variable(type, name,
                          alignvar?boffs(type, af.currentStackDepth):-(af.currentStackDepth + type.size));
  var.dontInit = dontInit;
  if (size) {
    mixin(mustOffset("size", "2"));
    auto vd = new VarDecl(var);;
    vd.emitAsm(af);
  }
  {
    mixin(mustOffset("0"));
    dg(var);
  }
}

void mkVar(AsmFile af, IType type, bool dontInit, void delegate(Variable) dg) {
  mkVar(af, type, dontInit, true, dg);
}

void mkVarUnaligned(AsmFile af, IType type, bool dontInit, void delegate(Variable) dg) {
  mkVar(af, type, dontInit, false, dg);
}

import tools.base;
LValue mkRef(AsmFile af, Expr ex, ref void delegate() post) {
  if (auto lv = fastcast!(LValue)~ ex)
    return lv;
  
  auto type = ex.valueType();
  int size = type.size;
  // void vars are fucking weird, yes.
  assert (type != Single!(Void));
  string name;
  static int x;
  synchronized name = Format("__temp_var_", x++, "__");
  auto var = new Variable(type, name,
                          boffs(type, af.currentStackDepth));
  var.initval = ex;
  post = stuple(af, af.checkptStack()) /apply/ (AsmFile af, typeof(af.checkptStack()) forble) { af.restoreCheckptStack(forble); };
  auto vd = new VarDecl(var);
  vd.emitAsm(af);
  return var;
}

Expr lvize_if_possible(Expr ex, Statement* late_init = null) {
  if (auto lv = fastcast!(LValue) (ex)) return ex;
  auto sc = namespace().get!(Scope);
  if (!sc) {
    return ex;
  }
  auto var = new Variable(ex.valueType(), null, boffs(ex.valueType()));
  // TODO: is it really valid to add to a scope beneath a nested namespace?
  // Won't this mess up the frame size counts? .. Meh.
  // NOTE: THIS IS VERY VERY VEEEEERRY IFFY
  // because it changes the semantics; specifically, the evaluation point of ex() to the variable declaration point
  // only use lvize() if you are aware of this!
  // NOTE: for this reason, late_init was added
  
  sc.add(var);
  
  if (late_init) {
    *late_init = new Assignment(var, ex);
    var.dontInit = true;
  } else {
    var.initval = ex;
  }
  
  auto decl = new VarDecl(var);
  sc.addStatement(decl);
  return var;
}

// create temporary if needed
extern(C) LValue ast_vardecl_lvize(Expr ex, Statement* late_init = null) {
  if (auto lv = fastcast!(LValue) (ex)) return lv;
  if (!namespace().get!(Scope)) {
    logln("No Scope beneath ", namespace(), " for lvizing ", ex, "!");
    fail;
  }
  return fastcast!(LValue) (lvize_if_possible(ex, late_init));
}

LValue lvize(Expr ex, Statement* late_init = null) { return ast_vardecl_lvize(ex, late_init); }

class WithTempExpr : Expr {
  OffsetExpr offs, offs_res;
  Expr thing, superthing;
  this(Expr thing, Expr delegate(Expr, OffsetExpr) dg) {
    offs = new OffsetExpr(int.max, thing.valueType());
    offs_res = new OffsetExpr(int.max, null);
    this.thing = thing;
    superthing = dg(offs, offs_res);
  }
  protected this() { }
  mixin defaultIterate!(thing, superthing);
  override {
    string toString() {
      return Format("<with temp ", thing, ": ", superthing, ">");
    }
    WithTempExpr dup() {
      auto res = new WithTempExpr;
      res.offs = new OffsetExpr(int.max, offs.type);
      res.offs_res = new OffsetExpr(int.max, offs_res.type);
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
    void emitAsm(AsmFile af) {
      if (superthing.valueType() == Single!(Void)) {
        thing.emitAsm(af);
        offs.offset = -af.currentStackDepth;
        {
          mixin(mustOffset("0"));
          superthing.emitAsm(af);
        }
        af.sfree(thing.valueType().size);
      } else {
        mkVar(af, superthing.valueType(), true, (Variable var) {
          offs_res.offset = var.baseOffset;
          thing.emitAsm(af);
          offs.offset = -af.currentStackDepth;
          (mkAssignment(var, superthing)).emitAsm(af);
          af.sfree(thing.valueType().size);
        });
      }
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

import ast.fold;
Expr mkTemp(AsmFile af, Expr ex, ref void delegate() post) {
  auto fex = foldex(ex);
  if (fastcast!(Literal)~ fex) return fex;
  return mkRef(af, fex, post);
}

import ast.namespace, ast.scopes, ast.aggregate, tools.compat: find;
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto sc = new Scope;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  string name; IType type;
  bool abortGracefully;
  if (rest(t2, "type", &type)) {
    if (t2.accept(":")) return null; // cast
    if (t2.accept("(")) return null; // compound var expr
    if (!t2.bjoin(t2.gotValidIdentifier(name), t2.accept(","), {
      auto var = new Variable;
      var.name = name;
      var.type = type;
      bool dontInit;
      if (t2.accept("<-")) { abortGracefully = true; return; } // aaaa
      if (t2.accept("=")) {
        IType[] its;
        auto t3 = t2;
        if ((!rest(t2, "tree.expr", &var.initval) || !gotImplicitCast(var.initval, var.type, (IType it) {
          its ~= it;
          return test(var.type == it);
        })) && (t2 = t3, true) && !(t2.accept("void") && (dontInit = true, true))) {
          if (its.length) t2.failparse("Couldn't init var; none of ", its, " matched ", var.type);
          else t2.failparse("Couldn't read expression");
        }
      }
      if (dontInit) {
        var.dontInit = true;
      } else {
        var.initInit();
        if (var.type != Single!(Void)) {
          assert(!!var.initval);
          if (var.type != var.initval.valueType())
            throw new Exception(Format("Mismatching types in initializer: ", var, " of ", var.type, " <- ", var.initval.valueType()));
        }
      }
      var.baseOffset = boffs(var.type);
      auto vd = new VarDecl(var);
      vd.configPosition(text);
      sc.addStatement(vd);
      sc.add(var); // was: namespace()
    }, false)) {
      if (abortGracefully) return null;
      t2.failparse("Couldn't parse variable declaration");
    }
    if (abortGracefully) return null;
    t2.mustAccept(";", "Missed trailing semicolon");
    text = t2;
    if (sc.guards.length) fail;
    // collapse
    foreach (entry; sc.field) {
      if (auto sa = fastcast!(SelfAdding) (entry._1)) if (sa.addsSelf()) continue;
      sc.sup.add(entry._0, entry._1);
    }
    return fastcast!(Object) (sc._body);
  } else return null;
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl", "21");

Object gotAutoDecl(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, varname;
  Expr ex;
  
  auto sc = new Scope;
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  
  string t3;
  resetError();
  if (!t2.accept("auto")) return null;
  if (t2.accept("(")) return null; // compound var expr
  while (true) {
    if (!t2.gotValidIdentifier(varname, true))
      t2.failparse("Could not get variable identifier");
    if (t2.accept("<-")) return null; // is an iterator-construct
    if (!t2.accept("="))
      t2.failparse("Could not get auto initializer");
    if (!rest(t2, "tree.expr", &ex))
      t2.failparse("Could not get auto init expression");
    auto var = new Variable;
    var.name = varname;
    var.initval = ex;
    var.type = ex.valueType();
    var.baseOffset = boffs(var.type);
    auto vd = new VarDecl(var);
    vd.configPosition(text);
    sc.addStatement(vd);
    sc.add(var); // was namespace()
    if (t2.accept(";")) break;
    if (t2.accept(",")) continue;
    t2.failparse("Unexpected text in auto expr");
  }
  text = t2;
  if (sc.guards.length) fail;
  // collapse
  foreach (entry; sc.field) {
    if (auto sa = fastcast!(SelfAdding) (entry._1)) if (sa.addsSelf()) continue;
    sc.sup.add(entry._0, entry._1);
  }
  return fastcast!(Object) (sc._body);
}
mixin DefaultParser!(gotAutoDecl, "tree.stmt.autodecl", "22");
