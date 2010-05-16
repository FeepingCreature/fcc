module ast.literals;

import ast.base, ast.pointer, tools.base: slice, replace, startsWith;

class StringExpr : Expr {
  string str;
  // default action: place in string segment, load address on stack
  override void emitAsm(AsmFile af) {
    auto name = Format("cons_", af.constants.length);
    af.constants[name] = cast(ubyte[]) str;
    af.pushStack("$"~name, valueType());
  }
  override Type valueType() { return Single!(Pointer, Single!(Char)); }
}

bool gotStringExpr(ref string text, out Expr ex) {
  auto t2 = text;
  StringExpr se;
  return t2.accept("\"") &&
    (se = new StringExpr, true) &&
    (se.str = t2.slice("\"").replace("\\n", "\n"), true) &&
    (text = t2, true) &&
    (ex = se, true);
}

class IntExpr : Expr {
  int num;
  override void emitAsm(AsmFile af) {
    af.pushStack(Format("$", num), valueType());
  }
  override Type valueType() { return Single!(SysInt); }
  this(int i) { num = i; }
}

bool gotIntExpr(ref string text, out Expr ex) {
  auto t2 = text.strip();
  if (auto rest = t2.startsWith("-")) {
    return gotIntExpr(rest, ex)
      && (
        ((cast(IntExpr) ex).num = -(cast(IntExpr) ex).num),
        (text = rest),
        true
      );
    }
  bool isNum(char c) { return c >= '0' && c <= '9'; }
  if (!t2.length || !isNum(t2[0])) return false;
  int res = t2.take() - '0';
  while (t2.length) {
    if (!isNum(t2[0])) break;
    res = res * 10 + t2.take() - '0'; 
  }
  ex = new IntExpr(res);
  text = t2;
  return true;
}
