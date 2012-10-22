module ast.returns;

import
  ast.base, ast.namespace, ast.scopes, ast.fun, ast.parse, ast.fun,
  ast.vardecl, ast.pointer, ast.math, ast.assign;

class ReturnStmt : Statement {
  Expr value;
  Namespace ns;
  this(Expr ex) {
    ns = namespace();
    value = ex; this();
  }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!(value);
  Statement[] guards;
  int[] guard_offsets;
  void setGuards(Scope sc) {
    guards = sc.getGuards();
    guard_offsets = sc.getGuardOffsets();
  }
  string toString() { return Format("return "[], value); }
  override void emitLLVM(LLVMFile lf) {
    auto fun = ns.get!(Function);
    
    void emitGuards() {
      foreach_reverse(i, stmt; guards) {
        stmt.dup().emitLLVM(lf);
      }
    }
    if (value) {
      {
        mixin(mustOffset("1"));
        value.emitLLVM(lf);
      }
      emitGuards();
      if (Single!(Void) == value.valueType()) {
        auto lp = lf.pop();
        if (lp != "void") {
          logln("garbage on stack at ret void: ", lp);
          fail;
        }
        put(lf, "ret void");
      } else {
        put(lf, "ret ", typeToLLVM(value.valueType()), " ", lf.pop());
      }
    } else emitGuards();
    // TODO: stack cleanup token here
    jump(lf, fun.exit());
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
    if (gotImplicitCast(rs.value, fun.type.ret, (IType it) { tried ~= it; return test(it == ret); }, false)) {
      return rs;
    }
    else {
      text.failparse("Could not convert to return type "[], fun.type.ret, "; expression had the type "[], temp.valueType());
    }
  }
  
  if (!fun.type.ret) fun.type.ret = Single!(Void);
  
  if (Single!(Void) == fun.type.ret)
    return rs; // permit no-expr
  text.failparse("Error parsing return expression"[]);
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return", "101", "return");
