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
      if (var.baseOffset + var.type.size != -af.currentStackDepth) {
        logln("Stack wrong for var emit: LOGIC ERROR; variable needs to start at ", var.baseOffset + var.type.size, " vs. stack at ", -af.currentStackDepth, ": ", var);
        foreach (elem; namespace().field) {
          if (auto var = cast(Variable) elem._1) {
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

// base offset
import tools.log;
int boffs(IType t, int curdepth = -1) {
  if (curdepth == -1) {
    auto sl = namespace().get!(ScopeLike);
    if (!sl) {
      logln("no ScopeLike beneath ", namespace(), " for placing a ", t);
      asm { int 3; }
    }
    curdepth = sl.framesize();
  }
  return - curdepth - t.size;
}

void mkVar(AsmFile af, IType type, bool dontInit, void delegate(Variable) dg) {
  int size = type.size;
  // void vars are fucking weird.
  if (type == Single!(Void)) size = 0;
  mixin(mustOffset("size"));
  string name;
  static int x;
  synchronized name = Format("__temp_var_", x++, "__");
  auto var = new Variable(type, name,
                          boffs(type, af.currentStackDepth));
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
  if (t2.accept("auto")) {
    if (!t2.bjoin(
    (t3 = t2, true) &&
    t3.gotIdentifier(varname, true) && t3.accept("=") && rest(t3, "tree.expr", &ex) && (t2 = t3, true),
    t2.accept(","), {
      auto var = new Variable;
      var.name = varname;
      var.initval = ex; var.type = ex.valueType();
      var.baseOffset = boffs(var.type);
      vd.vars ~= var;
      namespace().add(var);
    }, false)) {
      t3.failparse("Syntax error in auto decl: ", error()._1);
    }
    if (!t2.accept(";"))
      t2.failparse("auto decl not terminated");
    text = t2;
    return vd;
  } else return null;
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
