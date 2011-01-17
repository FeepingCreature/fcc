module ast.main;

import ast.base, ast.fun, ast.intrinsic, ast.modules, ast.namespace;
import ast.scopes, ast.arrays, ast.returns, ast.parse;

void fixupMain() {
  auto cmain = cast(Function) sysmod.lookup("_c_main");
  if (!cmain) { logln("fail 0: ", cmain); fail(); }
  auto sc = cast(Scope) cmain.tree;
  if (!sc) { logln("fail 1: ", cmain.tree); fail(); }
  auto argvar = cast(Expr) sc.lookup("args");
  if (!argvar) { logln("fail 2: ", sc.field); fail(); }
  if (!gotMain) {
    logln("main function not found! ");
    fail();
  }
  auto call = gotMain.mkCall();
  
  auto m = gotMain;
  bool mainReturnsInt, mainTakesStrings;
  if (m.type.ret == Single!(SysInt))
    mainReturnsInt = true;
  if (!m.type.params.length) { }
  else {
    if (m.type.params.length != 1) {
      logln("invalid main form: ", m.type);
      fail();
    }
    if (m.type.params[0]._0 == Single!(Array, Single!(Array, Single!(Char))))
      mainTakesStrings = true;
    else {
      logln("invalid main form: ", m.type);
      fail();
    }
  }
  
  if (mainTakesStrings) call.params ~= argvar;
  Statement res;
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(cmain);
  
  if (mainReturnsInt) res = new ReturnStmt(call);
  else res = new ExprStatement(call);
  sc.addStatement(res);
}
