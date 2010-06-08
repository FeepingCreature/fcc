module ast.literals;

import ast.base, ast.pointer, tools.base: slice, replace, startsWith;

public import ast.int_literal;

import ast.static_arrays, parseBase;

class StringExpr : Expr {
  string str;
  this() { }
  this(string s) { str = s; }
  string name_used;
  // default action: place in string segment, load address on stack
  override void emitAsm(AsmFile af) {
    assert(false, "Why are you pushing a string on the stack? This seems iffy to me. ");
    name_used = Format("cons_", af.constants.length);
    af.constants[name_used] = cast(ubyte[]) str;
    // af.pushStack("$"~name, valueType());
  }
  override Type valueType() { return new StaticArray(Single!(Char), str.length); }
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

Object gotLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (text.gotStringExpr(ex) || text.gotIntExpr(ex)) return cast(Object) ex;
  else return null;
}
mixin DefaultParser!(gotLiteralExpr, "tree.expr.literal", "5");
