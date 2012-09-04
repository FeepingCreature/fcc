module ast.returns;

import
  ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse, ast.fun,
  ast.vardecl, ast.pointer, ast.math, ast.assign;

class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  Expr myRetvalHolder;
  this(Expr ex) {
    ns = namespace();
    value = ex; this();
    myRetvalHolder = fastcast!(Expr) (ns.lookup("__retval_holder", true));
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(value, myRetvalHolder);
  Statement[] guards;
  int[] guard_offsets;
  void setGuards(Scope sc) {
    guards = sc.getGuards();
    guard_offsets = sc.getGuardOffsets();
    debug if (guards && !myRetvalHolder) {
      auto supfun = ns.get!(Function);
      if (supfun && supfun.type.ret && supfun.type.ret != Single!(Void)) {
        logln("WARN unsafe case");
        logln("for ", guards);
        logln("in ", ns);
      }
    }
  }
  string toString() { return Format("return "[], value); }
  override void emitAsm(AsmFile af) {
    auto fun = ns.get!(Function);
    
    auto backup = af.checkptStack();
    scope(exit) af.restoreCheckptStack(backup, true /* restoring to larger depth */);
    
    void emitGuards(bool mustPreserveStack) {
      foreach_reverse(i, stmt; guards) {
        auto delta = af.currentStackDepth - guard_offsets[i];
        if (delta) {
          if (mustPreserveStack) {
            logln("WARN this is unsafe: ", delta, " between ", af.currentStackDepth, " since we wanted [", i, "] ", guard_offsets[i]);
            logln("guard is ", stmt);
            logln("we are forced to use a wrong stack offset for a statement because the return type of a function was indeterminate when a retval holder was requested");
            // asm { int 3; }
          } else af.restoreCheckptStack(guard_offsets[i]);
        }
        // dup because we know this is safe for multi-emit; it may get emat multiple times, but it will only get called once.
        stmt.dup().emitAsm(af);
      }
    }
    if (value) {
      if (Single!(Void) == value.valueType()) {
        mixin(mustOffset("0"[]));
        scope(failure) logln("While returning ", value, " of ", value.valueType());
        value.emitAsm(af);
        emitGuards(false);
      } else {
        // mixin(mustOffset("0"[]));
        scope(failure) logln("while returning "[], value);
        auto vt = value.valueType();
        Expr value = myRetvalHolder;
        int tofree;
        scope(success) af.sfree(tofree);
        auto var = fastcast!(Variable) (value);
        if (value && !var) fail;
        if (guards && var && -var.baseOffset > af.currentStackDepth) {
          logln("var is ", var, " at ", -var.baseOffset, " while we're at ", af.currentStackDepth, ", with ", guards);
          fail;
        }
        if (var) {
          if (af.currentStackDepth != -var.baseOffset) {
            if (af.currentStackDepth > -var.baseOffset) {
              // af.restoreCheckptStack(-var.baseOffset);
            } else {
              logln("bad place to grab ", var, " for return: declared at ", -var.baseOffset, " currentStackDepth ", af.currentStackDepth, " btw ", guards);
              asm { int 3; }
            }
          }
          emitAssign(af, fastcast!(LValue) (value), this.value);
          emitGuards(false);
          if (af.currentStackDepth != -var.baseOffset) {
            if (af.currentStackDepth > -var.baseOffset) {
              af.restoreCheckptStack(-var.baseOffset);
            } else {
              logln("bad place to grab ", var, " for return: declared at ", -var.baseOffset, " currentStackDepth ", af.currentStackDepth, " btw ", guards);
            }
          }
        } else {
          tofree = alignStackFor(vt, af);
          var = fastalloc!(Variable)(vt, cast(string) null, boffs(vt, af.currentStackDepth));
          value = var;
          (fastalloc!(VarDecl)(var)).emitAsm(af);
          tofree += vt.size; // pro forma
          emitAssign(af, var, this.value);
          emitGuards(true);
        }
        
        if (vt.returnsInMemory()) {
          auto target = fastcast!(Expr) (namespace().lookup("__return_pointer"));
          if (!target) {
            logln("no return pointer found in function that demands one: ", namespace());
            fail;
          }
          emitAssign(af, new DerefExpr(target), value);
        } else if (Single!(Float) == vt) {
          loadFloatEx(value, af);
          af.floatStackDepth --; // doesn't count
        } else if (Single!(Double) == vt) {
          loadDoubleEx(value, af);
          af.floatStackDepth --; // doesn't count
        } else if (vt.size == 1) {
          af.salloc(3);
          value.emitAsm(af);
          if (isARM) {
            af.mmove1("[sp]"[], "r0"[]);
            af.sfree(1);
          } else {
            af.popStack("%al"[], 1);
          }
          af.sfree(3);
        } else if (vt.size == 2) {
          value.emitAsm(af);
          af.popStack("%ax"[], 2);
        } else if (vt.size == 4) {
          value.emitAsm(af);
          af.popStack(af.regs[0], 4);
        } else if (vt.size == 8) {
          value.emitAsm(af);
          af.popStack(af.regs[0], 4);
          af.popStack(af.regs[3], 4);
        // Well, C compatible this ain't.
        // TODO
        } else if (vt.size == 12) {
          value.emitAsm(af);
          with (af) {
            popStack(regs[0], 4);
            popStack(regs[2], 4);
            popStack(regs[3], 4);
          }
        } else if (vt.size == 16) {
          value.emitAsm(af);
          with (af) {
            popStack(regs[0], 4);
            popStack(regs[1], 4);
            popStack(regs[2], 4);
            popStack(regs[3], 4);
          }
        } else {
          logln("Unsupported return type "[], vt, "[], being "[], vt.size);
          fail;
        }
      }
    } else emitGuards(false);
    // TODO: stack cleanup token here
    af.jump(fun.exit(), true);
  }
}

import ast.casting;
Object gotRetStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto rs = new ReturnStmt(null);
  
  if (auto sc = fastcast!(Scope)~ namespace()) {
    rs.setGuards(sc);
  }
  
  auto fun = namespace().get!(Function)();
  text = t2;
  IType[] tried;
  if (rest(text, "tree.expr"[], &rs.value)) {
    auto temp = rs.value;
    
    // auto deduction!
    if (!fun.type.ret) {
      auto vt = rs.value.valueType();
      if (vt.returnsInMemory()) {
        // AAAAAAAAAAAAAAAAAaaaaaaaaaaaaaaaaaaaaa
        // panic panic panic
        vt = fastalloc!(NoNoDontReturnInMemoryWrapper)(vt);
        rs.value = reinterpret_cast(vt, rs.value);
      }
      fun.type.ret = rs.value.valueType();
    }
    
    auto ret = resolveType(fun.type.ret);
    if (gotImplicitCast(rs.value, fun.type.ret, (IType it) { tried ~= it; return test(it == ret); })) {
      return rs;
    }
    else {
      text.failparse("Could not convert to return type "[], fun.type.ret, "; expression had the type "[], temp.valueType());
    }
  }
  
  if (!fun.type.ret) fun.type.ret = Single!(Void);
  else if (fun.type.ret.size > 16)
    text.failparse("Return type cannot be larger than 16 bytes! "[]);
  
  if (Single!(Void) == fun.type.ret)
    return rs; // permit no-expr
  text.failparse("Error parsing return expression"[]);
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return", "20", "return");
