module ast.vardecl;

import ast.assign, ast.base, tools.base: Range;
public import ast.variable;

import ast.pointer, ast.casting;
class VarDecl : Statement {
  Variable[] vars;
  mixin DefaultDup!();
  mixin defaultIterate!(vars);
  override void emitAsm(AsmFile af) {
    // logln("emit at ", af.currentStackDepth, ": ", vars);
    foreach (var; vars) {
      // sanity checking start!
      if (var.baseOffset + var.type.size < -af.currentStackDepth) {
        auto delta = -af.currentStackDepth - (var.baseOffset + var.type.size);
        // logln("alloc ", delta, " to compensate for stack being wrong for var");
        // logln("(", var.name, " at ", af.currentStackDepth, " wants ", -var.baseOffset - var.type.size, ")");
        af.salloc(delta);
      }
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
        assert(false);
      }
      // sanity checking end!
      if (var.dontInit)
        af.salloc(var.type.size);
      else {
        if (var.type == Single!(Void)) {
          mixin(mustOffset("0"));
          if (var.initval) var.initval.emitAsm(af);
          continue;
        }
        mixin(mustOffset("var.type.size"));
        int sz = var.type.size;
        // TODO: investigate why necessary for chars
        if (sz == 1) af.salloc(1);
        var.initval.emitAsm(af);
        if (sz == 1) {
          var.emitLocation(af);
          af.popStack("%eax", new Pointer(var.valueType()));
          af.popStack("(%eax)", var.initval.valueType());
          af.nvm("%eax");
        }
      }
    }
  }
  override string toString() { return Format("declare ", vars); }
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
    auto vd = new VarDecl;
    vd.vars ~= var;
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
  auto vd = new VarDecl;
  vd.vars ~= var;
  vd.emitAsm(af);
  return var;
}

// create temporary if needed
LValue lvize(Expr ex) {
  if (auto lv = fastcast!(LValue)~ ex) return lv;
  
  auto var = new Variable(ex.valueType(), null, boffs(ex.valueType()));
  auto sc = fastcast!(Scope)~ namespace();
  assert(!!sc);
  var.initval = ex;
  
  auto decl = new VarDecl;
  decl.vars ~= var;
  var.baseOffset = boffs(ex.valueType());
  sc.addStatement(decl);
  sc.add(var);
  return var;
}

import ast.fold;
Expr mkTemp(AsmFile af, Expr ex, ref void delegate() post) {
  auto fex = foldex(ex);
  if (fastcast!(Literal)~ fex) return fex;
  return mkRef(af, fex, post);
}

import ast.namespace, ast.scopes, tools.compat: find;
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text, vd = new VarDecl;
  string name; IType type;
  if (rest(t2, "type", &type)) {
    if (!t2.bjoin(t2.gotIdentifier(name), t2.accept(","), {
      auto var = new Variable;
      var.name = name;
      var.type = type;
      bool dontInit;
      if (t2.accept("=")) {
        IType[] its;
        auto t3 = t2;
        if ((!rest(t2, "tree.expr", &var.initval) || !gotImplicitCast(var.initval, (IType it) {
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
            throw new Exception(Format("Mismatching types in initializer: ", var, " <- ", var.initval.valueType()));
        }
      }
      var.baseOffset = boffs(var.type);
      vd.vars ~= var;
      namespace().add(var);
    }, false))
      t2.failparse("Couldn't parse variable declaration");
    t2.mustAccept(";", "Missed trailing semicolon");
    text = t2;
    return vd;
  } else return null;
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl", "21");

Object gotAutoDecl(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, varname;
  Expr ex;
  auto vd = new VarDecl;
  string t3;
  resetError();
  if (!t2.accept("auto")) return null;
  while (true) {
    if (!t2.gotIdentifier(varname, true))
      t2.failparse("Could not get variable identifier! ");
    if (!t2.accept("="))
      t2.failparse("Could not get auto initializer! ");
    if (!rest(t2, "tree.expr", &ex))
      t2.failparse("Could not get auto init expression! ");
    auto var = new Variable;
    var.name = varname;
    var.initval = ex;
    var.type = ex.valueType();
    var.baseOffset = boffs(var.type);
    vd.vars ~= var;
    namespace().add(var);
    if (t2.accept(";")) break;
    if (t2.accept(",")) continue;
    t2.failparse("Unexpected text in auto expr");
  }
  text = t2;
  return vd;
}
mixin DefaultParser!(gotAutoDecl, "tree.stmt.autodecl", "22");

Object gotVarDeclExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  IType type;
  if (!t2.accept("auto"))
    if (!rest(t2, "type", &type)) return null;
  if (!t2.gotIdentifier(name)) return null;
  bool dontInit;
  Expr initval;
  if (t2.accept("=")) {
    IType[] its;
    if (!rest(t2, "tree.expr", &initval)
      || type && !gotImplicitCast(initval, type, (IType it) {
      its ~= it;
      return test(type == it);
    }))
      t2.failparse("Could not parse variable initializer; tried ", its);
    if (!type) type = initval.valueType();
  } else {
    if (!type) {
      t2.setError("Auto vardecl exprs must be initialized. ");
      return null;
    }
  }
  
  auto var = new Variable(type, name, boffs(type));
  namespace().get!(Scope).add(var);
  auto vd = new VarDecl;
  vd.vars ~= var;
  namespace().get!(Scope).addStatement(vd);

  text = t2;
  if (!initval) { var.initInit; return var; }
  var.dontInit = true;
  auto setVar = new Assignment(var, initval);
  return new StatementAndExpr(setVar, var);
}
mixin DefaultParser!(gotVarDeclExpr, "tree.expr.vardecl", "28");
