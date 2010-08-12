module ast.vardecl;

import ast.assign, ast.base;
public import ast.variable;

class VarDecl : Statement {
  Variable[] vars;
  bool dontInit;
  mixin defaultIterate!(vars);
  override void emitAsm(AsmFile af) {
    logln("emit at ", af.currentStackDepth, ": ", vars);
    foreach (var; vars) {
      af.salloc(var.type.size);
      // if (-var.baseOffset != af.currentStackDepth) asm { int 3; }
      assert(-var.baseOffset == af.currentStackDepth, Format("Variable mispositioned: LOGIC ERROR; ", -var.baseOffset, " vs. ", af.currentStackDepth, ": ", var));
      af.comment("init ", var);
      if (!dontInit)
        (new Assignment(var, var.initval)).emitAsm(af);
    }
  }
}

// base offset
import tools.log;
int boffs(IType t, int curdepth = -1) {
  auto sl = namespace().get!(ScopeLike);
  assert(!!sl);
  if (curdepth == -1)
    curdepth = sl.framesize();
  return - curdepth - t.size;
}

static int x;
void mkVar(AsmFile af, IType type, bool dontInit, void delegate(Variable) dg) {
  mixin(mustOffset("type.size"));
  auto var = new Variable(type, Format("__temp_var_", x++, "__"),
                          boffs(type, af.currentStackDepth));
  auto vd = new VarDecl;
  vd.vars ~= var;
  vd.dontInit = dontInit;
  vd.emitAsm(af);
  {
    mixin(mustOffset("0"));
    dg(var);
  }
}

import ast.namespace, ast.scopes;
Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text, vd = new VarDecl;
  string name; IType type;
  if (rest(t2, "type", &type)) {
    if (!t2.bjoin(t2.gotIdentifier(name), t2.accept(","), {
      auto var = new Variable;
      var.name = name;
      var.type = type;
      if (t2.accept("=")) {
        if (!rest(t2, "tree.expr", &var.initval, delegate bool(Expr ex) {
          if (var.type != ex.valueType()) {
            error = Format("mismatched types in init: ", var.type, " = ", ex.valueType());
          }
          return !!(var.type == ex.valueType());
        }))
          throw new Exception(Format("Couldn't read expression at ", t2.next_text(), ": ", error));
      }
      var.initInit();
      assert(var.initval);
      if (var.type != var.initval.valueType())
        throw new Exception(Format("Mismatching types in initializer: ", var, " <- ", var.initval.valueType()));
      var.baseOffset = boffs(var.type);
      vd.vars ~= var;
      namespace().add(var);
    }, false))
      throw new Exception("Couldn't parse variable declaration at "~t2.next_text());
    t2.mustAccept(";", Format("Missed trailing semicolon at ", t2.next_text()));
    text = t2;
    return vd;
  } else return null;
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl");

Object gotAutoDecl(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, varname;
  Expr ex;
  auto vd = new VarDecl;
  if (t2.accept("auto")) {
    if (!t2.bjoin(
    t2.gotIdentifier(varname, true) && t2.accept("=") && rest(t2, "tree.expr", &ex),
    t2.accept(","), {
      auto var = new Variable;
      var.initval = ex; var.type = ex.valueType();
      var.baseOffset = boffs(var.type);
      vd.vars ~= var;
      namespace().add(var);
    }, false)) {
      throw new Exception("Syntax error in auto decl at "~t2.next_text());
    }
    if (!t2.accept(";")) throw new Exception("auto decl not terminated at "~t2.next_text());
    text = t2;
    return vd;
  } else return null;
}
mixin DefaultParser!(gotAutoDecl, "tree.stmt.autodecl");
