module ast.returns;

import ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse, ast.math: loadFloatEx;

class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  mixin defaultIterate!(value);
  Statement[] guards;
  override void emitAsm(AsmFile af) {
    
    foreach_reverse(stmt; guards)
      stmt.emitAsm(af);
    
    auto fun = ns.get!(Function);
    if (value) {
      if (Single!(Float) == value.valueType()) {
        loadFloatEx(value, af);
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
      } else {
        assert(false, Format("Unsupported return type ", value.valueType()));
      }
    }
    // TODO: stack cleanup token here
    af.jump(fun.exit());
  }
}

Object gotRetStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("return")) {
    
    auto rs = new ReturnStmt;
    rs.ns = namespace();
    
    // TODO: gather guards from all scopes
    if (auto sc = cast(Scope) namespace())
      rs.guards = sc.getGuards();
    
    auto fun = namespace().get!(Function)();
    text = t2;
    if (fun.type.ret == Single!(Void))
      return rs; // don't expect a value.
    if (rest(text, "tree.expr", &rs.value, (Expr ex) {
      return !!(ex.valueType() == fun.type.ret);
    })) {
      return rs;
    } else throw new Exception("Error parsing return expression at "~text.next_text());
  } else return null;
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return", "3");
