module ast.literals;

import ast.base, ast.pointer, tools.base: slice, replace, startsWith;

class StringExpr : Expr {
  string str;
  this() { }
  this(string s) { str = s; }
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
  int i;
  return text.gotInt(i) && (ex = new IntExpr(i), true);
}

import parseBase;
Object gotLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (text.gotStringExpr(ex) || text.gotIntExpr(ex)) return cast(Object) ex;
  else return null;
}
mixin DefaultParser!(gotLiteralExpr, "tree.expr.literal", "5");
