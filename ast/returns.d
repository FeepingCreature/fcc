module ast.returns;

import ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse, ast.math: loadFloatEx;

import ast.vardecl, ast.assign, ast.math;
class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(value);
  Statement[] guards;
  override void emitAsm(AsmFile af) {
    auto fun = ns.get!(Function);
    void emitGuards() {
      foreach_reverse(stmt; guards)
        stmt.emitAsm(af);
    }
    if (value) {
      if (value.valueType() == Single!(Void)) {
        scope(failure) logln("While returning ", value, " of ", value.valueType());
        mixin(mustOffset("0"));
        value.emitAsm(af);
        emitGuards();
      } else {
        scope(failure) logln("while returning ", value);
        mixin(mustOffset("0"));
        auto value = new Variable(value.valueType(), null, boffs(value.valueType(), af.currentStackDepth));
        {
          auto vd = new VarDecl;
          vd.vars ~= value;
          vd.emitAsm(af);
        }
        (new Assignment(value, this.value)).emitAsm(af);
        emitGuards();
        
        if (Single!(Float) == value.valueType()) {
          loadFloatEx(value, af);
          af.floatStackDepth --; // doesn't count
        } else if (Single!(Double) == value.valueType()) {
          loadFloatEx(new DoubleAsFloat(value), af);
          af.floatStackDepth --; // doesn't count
        } else if (value.valueType().size == 4) {
          value.emitAsm(af);
          af.popStack("%eax", value.valueType());
        } else if (value.valueType().size == 8) {
          value.emitAsm(af);
          af.popStack("%eax", Single!(SizeT));
          af.popStack("%edx", Single!(SizeT));
        // Well, C compatible this ain't.
        // TODO
        } else if (value.valueType().size == 12) {
          value.emitAsm(af);
          af.popStack("%eax", Single!(SizeT));
          af.popStack("%ecx", Single!(SizeT));
          af.popStack("%edx", Single!(SizeT));
        } else if (value.valueType().size == 16) {
          value.emitAsm(af);
          af.popStack("%eax", Single!(SizeT));
          af.popStack("%ebx", Single!(SizeT));
          af.popStack("%ecx", Single!(SizeT));
          af.popStack("%edx", Single!(SizeT));
        } else {
          assert(false, Format("Unsupported return type ", value.valueType()));
        }
        af.sfree(value.valueType().size); // pro forma
      }
    } else emitGuards();
    // TODO: stack cleanup token here
    af.jump(fun.exit());
  }
}

import ast.casting;
Object gotRetStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto rs = new ReturnStmt;
  rs.ns = namespace();
  
  // TODO: gather guards from all scopes
  if (auto sc = cast(Scope) namespace())
    rs.guards = sc.getGuards();
  
  auto fun = namespace().get!(Function)();
  text = t2;
  if (rest(text, "tree.expr", &rs.value) && gotImplicitCast(rs.value, fun.type.ret, (IType it) { /*logln(it, " vs. ", fun.type.ret);*/ return test(it == fun.type.ret); }))
    return rs;
  if (fun.type.ret == Single!(Void))
    return rs; // permit no-expr
  text.failparse("Error parsing return expression");
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return", "3", "return");
