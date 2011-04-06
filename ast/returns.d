module ast.returns;

import ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse, ast.math: loadFloatEx;

import ast.vardecl, ast.assign, ast.math;
class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  this(Expr ex) { ns = namespace(); value = ex; this(); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(value);
  Statement[] guards;
  override void emitAsm(AsmFile af) {
    auto fun = ns.get!(Function);
    void emitGuards() {
      foreach_reverse(stmt; guards)
        stmt.dup().emitAsm(af);
    }
    if (value) {
      if (value.valueType() == Single!(Void)) {
        scope(failure) logln("While returning ", value, " of ", value.valueType());
        mixin(mustOffset("0"));
        value.emitAsm(af);
        emitGuards();
      } else {
        scope(failure) logln("while returning ", value);
        auto vt = value.valueType();
        int filler = alignStackFor(vt, af);
        scope(success) af.sfree(filler);
        mixin(mustOffset("0"));
        auto value = new Variable(vt, null, boffs(vt, af.currentStackDepth));
        {
          auto vd = new VarDecl;
          vd.vars ~= value;
          vd.emitAsm(af);
        }
        (new Assignment(value, this.value)).emitAsm(af);
        emitGuards();
        
        if (Single!(Float) == vt) {
          loadFloatEx(value, af);
          af.floatStackDepth --; // doesn't count
        } else if (Single!(Double) == vt) {
          loadDoubleEx(value, af);
          af.floatStackDepth --; // doesn't count
        } else if (vt.size == 4) {
          value.emitAsm(af);
          af.popStack("%eax", 4);
        } else if (vt.size == 8) {
          value.emitAsm(af);
          af.popStack("%eax", 4);
          af.popStack("%edx", 4);
        // Well, C compatible this ain't.
        // TODO
        } else if (vt.size == 12) {
          value.emitAsm(af);
          af.popStack("%eax", 4);
          af.popStack("%ecx", 4);
          af.popStack("%edx", 4);
        } else if (vt.size == 16) {
          value.emitAsm(af);
          af.popStack("%eax", 4);
          af.popStack("%ebx", 4);
          af.popStack("%ecx", 4);
          af.popStack("%edx", 4);
        } else {
          assert(false, Format("Unsupported return type ", vt));
        }
        af.sfree(vt.size); // pro forma
      }
    } else emitGuards();
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
  if (auto sc = fastcast!(Scope)~ namespace())
    rs.guards = sc.getGuards();
  
  auto fun = namespace().get!(Function)();
  text = t2;
  IType[] tried;
  if (rest(text, "tree.expr", &rs.value)) {
    auto temp = rs.value;
    auto ret = resolveType(fun.type.ret);
    if (gotImplicitCast(rs.value, fun.type.ret, (IType it) { tried ~= it; return test(it == ret); }))
      return rs;
    else {
      text.failparse("Could not convert ", temp, " to ", fun.type.ret, " for return: tried ", tried);
    }
  }
  if (fun.type.ret == Single!(Void))
    return rs; // permit no-expr
  text.failparse("Error parsing return expression");
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return", "3", "return");
