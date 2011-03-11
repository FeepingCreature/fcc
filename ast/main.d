module ast.main;

import ast.base, ast.fun, ast.intrinsic, ast.modules, ast.namespace,
  ast.scopes, ast.arrays, ast.returns, ast.parse, ast.pointer, ast.opers,
  ast.casting, ast.int_literal, ast.funcall, ast.tuples, ast.returns;

void fixupMain() {
  void fixupSpecificMain(Function cmain, bool isWinMain) {
    auto sc = fastcast!(Scope) (cmain.tree);
    if (!sc) { logln("fail 11: ", cmain.tree); fail(); }
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(cmain);
    
    sc.addStatement(new ReturnStmt(new CallbackExpr(Single!(SysInt), null, stuple(sc, isWinMain) /apply/ (Scope sc, bool isWinMain, Expr bogus, AsmFile af) {
      af.mmove4("$_sys_tls_data_start", "%esi"); // set up first tls pointer
      if (af.currentStackDepth != 4) // scrap space for ReturnStmt
        throw new Exception("stack depth assumption violated");
      // time for MAGIC
      int magic;
      if (isWinMain) {
        auto cvar = mkInt(1), pvar = new RefExpr(fastcast!(CValue) (sc.lookup("cmdline")));
        cvar.emitAsm(af);
        pvar.emitAsm(af);
        magic = 12;
      } else {
        auto cvar = fastcast!(Expr) (sc.lookup("argc")), pvar = fastcast!(Expr) (sc.lookup("argv"));
        cvar.emitAsm(af);
        pvar.emitAsm(af);
        magic = 12;
      }
      af.popStack("%eax", voidp);
      af.popStack("%ebx", Single!(SysInt));
      af.mathOp("andl", "$-16", "%esp"); // This is where the magic happens,
      af.salloc(magic); // magic constant align to 16
      af.pushStack("%ebp", voidp);
      af.mmove4("%esp", "%ebp");
      af.pushStack("%ebx", Single!(SysInt));
      af.pushStack("%eax", voidp);
      af.currentStackDepth = nativePtrSize * 2;
      auto ncvar = new DerefExpr(lookupOp("-",
        reinterpret_cast(Single!(Pointer, Single!(SysInt)), Single!(RegExpr, "%ebp")),
        mkInt(1) // Pointer math!
      ));
      auto npvar = new DerefExpr(lookupOp("-",
        reinterpret_cast(Single!(Pointer, Single!(Pointer, Single!(Pointer, Single!(Char)))), Single!(RegExpr, "%ebp")),
        mkInt(2)
      ));
      buildFunCall(
        fastcast!(Function) (sysmod.lookup("main2")),
        mkTupleExpr(ncvar, npvar),
        "main2 aligned call"
      ).emitAsm(af);
      // undo the alignment
      af.popStack("%eax", Single!(SysInt));
      af.sfree(af.currentStackDepth);
      af.popStack("%ebp", voidp);
      af.mmove4("%ebp", "%esp");
      af.currentStackDepth = 4;
      af.pushStack("%eax", Single!(SysInt)); // return this
    })));
  }
  auto cmain = fastcast!(Function) (sysmod.lookup("__c_main"));
  if (!cmain) { logln("fail 00"); fail(); }
  fixupSpecificMain(cmain, false);
  auto winmain = fastcast!(Function) (sysmod.lookup("__win_main"));
  if (!winmain) { logln("fail 20"); fail(); }
  fixupSpecificMain(winmain, true);
  
  auto main2 = fastcast!(Function)~ sysmod.lookup("main2");
  if (!main2) { logln("fail 10"); fail(); }
  auto sc = fastcast!(Scope)~ main2.tree;
  if (!sc) { logln("fail 11: ", main2.tree); fail(); }
  auto argvar = fastcast!(Expr)~ sc.lookup("args");
  if (!argvar) { logln("fail 12: ", sc.field); fail(); }
  auto cvar = fastcast!(Expr)~ sc.lookup("argc"), pvar = fastcast!(Expr)~ sc.lookup("argv");
  if (!gotMain) {
    logln("main function not found! ");
    fail();
  }
  auto call = gotMain.mkCall();
  
  auto m = gotMain;
  bool mainReturnsInt, mainTakesStrings, mainTakesArgCV; // argc, argv
  with (m.type) {
    if (ret == Single!(SysInt))
      mainReturnsInt = true;
    if (!params.length) { }
    else {
      if (params.length == 2) {
        if (params[0].type == Single!(SysInt) && params[1].type == Single!(Pointer, Single!(Pointer, Single!(Char))))
          mainTakesArgCV = true;
        else {
          logln("invalid main form (1): ", m.type);
          fail();
        }
      } else if (params.length == 1) {
        if (params[0].type == Single!(Array, Single!(Array, Single!(Char))))
          mainTakesStrings = true;
        else {
          logln("invalid main form (2): ", m.type);
          fail();
        }
      } else {
        logln("invalid main form (3): ", m.type);
        fail();
      }
    }
  }
  
  if (mainTakesStrings) call.params ~= argvar;
  if (mainTakesArgCV) call.params ~= [cvar, pvar];
  Statement res;
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(main2);
  
  if (mainReturnsInt) res = new ReturnStmt(call);
  else res = new ExprStatement(call);
  sc.addStatement(res);
}
