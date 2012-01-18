module ast.returns;

import ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse, ast.fun, ast.math: loadFloatEx;

import ast.vardecl, ast.assign, ast.math;
class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  this(Expr ex) { ns = namespace(); value = ex; this(); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(value);
  Statement[] guards;
  int[] guard_offsets;
  string toString() { return Format("return ", value); }
  override void emitAsm(AsmFile af) {
    auto fun = ns.get!(Function);
    
    auto backup = af.checkptStack();
    scope(exit) af.restoreCheckptStack(backup, true /* restoring to larger depth */);
    
    void emitGuards(bool mustPreserveStack) {
      foreach_reverse(i, stmt; guards) {
        auto delta = af.currentStackDepth - guard_offsets[i];
        if (delta) {
          if (mustPreserveStack) {
            logln("WARN this may break");
          } else af.restoreCheckptStack(guard_offsets[i]);
        }
        stmt.dup().emitAsm(af);
      }
    }
    if (value) {
      if (value.valueType() == Single!(Void)) {
        mixin(mustOffset("0"));
        scope(failure) logln("While returning ", value, " of ", value.valueType());
        value.emitAsm(af);
        emitGuards(false);
      } else {
        // mixin(mustOffset("0"));
        scope(failure) logln("while returning ", value);
        auto vt = value.valueType();
        Expr value = fastcast!(Expr) (ns.lookup("__retval_holder"));
        int tofree;
        scope(success) af.sfree(tofree);
        auto var = fastcast!(Variable) (value);
        if (value && (!var || -var.baseOffset <= af.currentStackDepth)) {
          (new Assignment(fastcast!(LValue) (value), this.value)).emitAsm(af);
          emitGuards(false);
          if (!var) fail;
          if (af.currentStackDepth != -var.baseOffset) {
            logln("bad place to grab ", var, " for return: declared at ", var.baseOffset, " currentStackDepth ", af.currentStackDepth);
          }
        } else {
          tofree = alignStackFor(vt, af);
          var = new Variable(vt, null, boffs(vt, af.currentStackDepth));
          value = var;
          (new VarDecl(var)).emitAsm(af);
          tofree += vt.size; // pro forma
          (new Assignment(var, this.value)).emitAsm(af);
          emitGuards(true);
        }
        
        if (Single!(Float) == vt) {
          loadFloatEx(value, af);
          af.floatStackDepth --; // doesn't count
        } else if (Single!(Double) == vt) {
          loadDoubleEx(value, af);
          af.floatStackDepth --; // doesn't count
        } else if (vt.size == 1) {
          af.salloc(3);
          value.emitAsm(af);
          if (isARM) {
            af.mmove1("[sp]", "r0");
            af.sfree(1);
          } else {
            af.popStack("%al", 1);
          }
          af.sfree(3);
        } else if (vt.size == 2) {
          value.emitAsm(af);
          af.popStack("%ax", 2);
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
          logln("Unsupported return type ", vt, ", being ", vt.size);
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
  auto rs = new ReturnStmt;
  rs.ns = namespace();
  
  // TODO: gather guards from all scopes
  if (auto sc = fastcast!(Scope)~ namespace()) {
    rs.guards = sc.getGuards();
    rs.guard_offsets = sc.getGuardOffsets();
  }
  
  auto fun = namespace().get!(Function)();
  text = t2;
  IType[] tried;
  if (rest(text, "tree.expr", &rs.value)) {
    auto temp = rs.value;
    
    // auto deduction!
    if (!fun.type.ret) fun.type.ret = rs.value.valueType();
    
    auto ret = resolveType(fun.type.ret);
    if (gotImplicitCast(rs.value, fun.type.ret, (IType it) { tried ~= it; return test(it == ret); }))
      return rs;
    else {
      text.failparse("Could not convert ", temp, " to ", fun.type.ret, " for return: tried ", tried);
    }
  }
  
  if (!fun.type.ret) fun.type.ret = Single!(Void);
  
  if (fun.type.ret == Single!(Void))
    return rs; // permit no-expr
  text.failparse("Error parsing return expression");
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return", "3", "return");
