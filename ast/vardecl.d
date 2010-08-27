module ast.vardecl;

import ast.assign, ast.base;
public import ast.variable;

import ast.pointer;
class VarDecl : Statement {
  Variable[] vars;
  mixin defaultIterate!(vars);
  override void emitAsm(AsmFile af) {
    // logln("emit at ", af.currentStackDepth, ": ", vars);
    foreach (var; vars) {
      if (var.dontInit)
        af.salloc(var.type.size);
      else {
        mixin(mustOffset("var.type.size"));
        int sz = var.type.size;
        // TODO: investigate why necessary for chars
        if (sz == 1) af.salloc(1);
        var.initval.emitAsm(af);
        if (sz == 1) {
          var.emitLocation(af);
          af.popStack("%eax", new Pointer(var.valueType()));
          af.popStack("(%eax)", var.initval.valueType());
        }
      }
      assert(-var.baseOffset == af.currentStackDepth, Format("Variable mispositioned: LOGIC ERROR; ", -var.baseOffset, " vs. ", af.currentStackDepth, ": ", var));
    }
  }
}

// base offset
import tools.log;
int boffs(IType t, int curdepth = -1) {
  auto sl = namespace().get!(ScopeLike);
  if (!sl) asm { int 3; }
  assert(!!sl, Format("no ScopeLike beneath ", namespace(), " for placing a ", t));
  if (curdepth == -1)
    curdepth = sl.framesize();
  return - curdepth - t.size;
}

static int x;
void mkVar(AsmFile af, IType type, bool dontInit, void delegate(Variable) dg) {
  mixin(mustOffset("type.size"));
  auto var = new Variable(type, Format("__temp_var_", x++, "__"),
                          boffs(type, af.currentStackDepth));
  var.dontInit = dontInit;
  auto vd = new VarDecl;
  vd.vars ~= var;
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
      bool dontInit;
      if (t2.accept("=")) {
        if (!rest(t2, "tree.expr", &var.initval, delegate bool(Expr ex) {
          if (var.type != ex.valueType()) {
            error = Format("mismatched types in init: ", var.type, " = ", ex.valueType());
          }
          return !!(var.type == ex.valueType());
        }) && !(t2.accept("void"), dontInit = true))
          throw new Exception(Format("Couldn't read expression at ", t2.next_text(), ": ", error));
      }
      if (dontInit) {
        var.dontInit = true;
      } else {
        var.initInit();
        assert(var.initval);
        if (var.type != var.initval.valueType())
          throw new Exception(Format("Mismatching types in initializer: ", var, " <- ", var.initval.valueType()));
      }
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
  string t3;
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
      throw new Exception("Syntax error in auto decl at '"~t3.next_text()~"'");
    }
    if (!t2.accept(";")) throw new Exception("auto decl not terminated at "~t2.next_text());
    text = t2;
    return vd;
  } else return null;
}
mixin DefaultParser!(gotAutoDecl, "tree.stmt.autodecl");
