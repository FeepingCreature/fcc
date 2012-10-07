module ast.main;

import ast.base, ast.fun, ast.intrinsic, ast.modules, ast.namespace,
  ast.scopes, ast.arrays, ast.returns, ast.parse, ast.pointer, ast.opers,
  ast.casting, ast.int_literal, ast.funcall, ast.tuples, ast.returns, ast.literals;

void fixupMain() {
  void fixupSpecificMain(Function cmain, bool isWinMain) {
    cmain.parseMe;
    auto sc = fastcast!(Scope) (cmain.tree);
    if (!sc) { logln("fail 11: "[], cmain.tree); fail(); }
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(cmain);
    
    sc.addStatement(fastalloc!(ReturnStmt)(fastalloc!(CallbackExpr)("main"[], Single!(SysInt), cast(Expr) null,
    stuple(sc, isWinMain) /apply/ (Scope sc, bool isWinMain, Expr bogus, LLVMFile lf) {
      // set up first tls pointer
      todo("main fixup callback");
      /*if (isARM) {
        lf.mmove4("=_sys_tls_data_start"[], "r4"[]);
      } else {
        lf.mmove4("$_sys_tls_data_start"[], "%esi"[]);
      }
      if (lf.currentStackDepth != 4 && !isARM) // scrap space for ReturnStmt
        throw new Exception(Format("stack depth assumption violated ("[], lf.currentStackDepth, ")"[]));
      // time for MAGIC
      int magic;
      Expr cvar, pvar;
      if (isWinMain) {
        cvar = mkInt(1); pvar = fastalloc!(RefExpr)(fastcast!(CValue) (sc.lookup("cmdline"[])));
      } else {
        cvar = fastcast!(Expr) (sc.lookup("argc"[])); pvar = fastcast!(Expr) (sc.lookup("argv"[]));
      }
      if (isARM) {
        buildFunCall(
          fastcast!(Function) (sysmod.lookup("main2"[])),
          mkTupleExpr(cvar, pvar),
          "main2 aligned call"
        ).emitLLVM(lf);
      } else {
        cvar.emitLLVM(lf);
        pvar.emitLLVM(lf);
        magic = isWinMain?4:4; // stack aligned -> call(<-4) -> push ebp
        lf.popStack("%eax"[], nativePtrSize);
        lf.popStack("%edx"[], 4);
        lf.mathOp("andl"[], "$-16"[], "%esp"[]); // This is where the magic happens,
        lf.salloc(magic); // magic constant align pretend-base to 16
        lf.pushStack("%ebp"[], nativePtrSize);
        lf.mmove4("%esp"[], "%ebp"[]);
        lf.pushStack("%edx"[], 4);
        lf.pushStack("%eax"[], nativePtrSize);
        lf.flush; // avoid problems when force changing the stack depth
        lf.currentStackDepth = nativePtrSize * 2;
        auto ncvar = fastalloc!(DerefExpr)(lookupOp("-"[],
          reinterpret_cast(Single!(Pointer, Single!(SysInt)), Single!(RegExpr, "%ebp"[])),
          mkInt(1) // Pointer math!
        ));
        auto npvar = fastalloc!(DerefExpr)(lookupOp("-"[],
          reinterpret_cast(Single!(Pointer, Single!(Pointer, Single!(Pointer, Single!(Char)))), Single!(RegExpr, "%ebp"[])),
          mkInt(2)
        ));
        buildFunCall(
          fastcast!(Function) (sysmod.lookup("main2"[])),
          mkTupleExpr(ncvar, npvar),
          "main2 aligned call"
        ).emitLLVM(lf);
        // undo the alignment
        lf.popStack("%eax"[], 4);
        lf.sfree(lf.currentStackDepth);
        lf.popStack("%ebp"[], nativePtrSize);
        lf.mmove4("%ebp"[], "%esp"[]);
        lf.currentStackDepth = 4;
        lf.pushStack("%eax"[], 4); // return this
      }*/
    })));
  }
  auto backupmod = current_module();
  current_module.set(fastcast!(Module) (sysmod));
  scope(exit) current_module.set(backupmod);
  
  logln("todo main fixup");
  return;
  auto cmain = fastcast!(Function) (sysmod.lookup("__c_main"[]));
  if (!cmain) { logln("fail 00"[]); fail(); }
  fixupSpecificMain(cmain, false);
  auto winmain = fastcast!(Function) (sysmod.lookup("__win_main"[]));
  if (!winmain) { logln("fail 20"[]); fail(); }
  fixupSpecificMain(winmain, true);
  
  auto main2 = fastcast!(Function)~ sysmod.lookup("main2"[]);
  if (!main2) { logln("fail 10"[]); fail(); }
  main2.parseMe;
  auto sc = fastcast!(Scope)~ main2.tree;
  if (!sc) { logln("fail 11: "[], main2.tree); fail(); }
  auto argvar = fastcast!(Expr)~ sc.lookup("args"[]);
  if (!argvar) { logln("fail 12: "[], sc.field, " "[], main2.field); fail(); }
  auto cvar = fastcast!(Expr)~ sc.lookup("argc"[]), pvar = fastcast!(Expr)~ sc.lookup("argv"[]);
  if (!gotMain) {
    logln("main function not found! "[]);
    fail();
  }
  auto call = gotMain.mkCall();
  
  auto m = gotMain;
  bool mainReturnsInt, mainTakesStrings, mainTakesArgCV; // argc, argv
  with (m.type) {
    if (Single!(SysInt) == ret)
      mainReturnsInt = true;
    if (!params.length) { }
    else {
      if (params.length == 2) {
        if (Single!(SysInt) == params[0].type && Single!(Pointer, Single!(Pointer, Single!(Char))) == params[1].type)
          mainTakesArgCV = true;
        else {
          logln("invalid main form (1): "[], m.type);
          fail();
        }
      } else if (params.length == 1) {
        if (Single!(Array, Single!(Array, Single!(Char))) == params[0].type)
          mainTakesStrings = true;
        else {
          logln("invalid main form (2): "[], m.type);
          fail();
        }
      } else {
        logln("invalid main form (3): "[], m.type);
        fail();
      }
    }
  }
  
  if (mainTakesStrings) call.params ~= argvar;
  if (mainTakesArgCV) call.params ~= [cvar, pvar];
  
  auto backup = namespace();
  scope(exit) namespace.set(backup);
  namespace.set(main2);
  
  Statement doReturn(Expr ex) {
    auto exitfn = new Function;
    with (exitfn) {
      name = "exit";
      type = new FunctionType;
      type.ret = Single!(Void);
      type.params ~= Argument(Single!(SysInt));
      extern_c = true;
    }
    return fastalloc!(ExprStatement)(buildFunCall(exitfn, ex, "exit call"[]));
  }
  
  if (mainReturnsInt) {
    sc.addStatement(doReturn(call));
  } else {
    sc.addStatement(fastalloc!(ExprStatement)(call));
    sc.addStatement(doReturn(fastalloc!(IntExpr)(0)));
  }
}
