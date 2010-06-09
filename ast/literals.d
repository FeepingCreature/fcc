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
  void loadConst(AsmFile af) {
    name_used = Format("cons_", af.constants.length);
    af.constants[name_used] = cast(ubyte[]) str;
  }
  override void emitAsm(AsmFile af) {
    assert(false, "Why are you pushing a string on the stack? This seems iffy to me. ");
    af.pushStack("$"~name_used, valueType());
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

/// "foo": char[3] -> char*
class StringAsPointer : Expr {
  StringExpr sup;
  mixin This!("sup");
  override Type valueType() { return Single!(Pointer, Single!(Char)); }
  override void emitAsm(AsmFile af) {
    sup.loadConst(af);
    af.pushStack("$"~sup.name_used, valueType());
  }
}

Object gotStringAsPointer(ref string st, ParseCb cont, ParseCb rest) {
  auto res = cast(StringExpr) cont(st);
  if (!res) return null;
  return new StringAsPointer(res);
}
mixin DefaultParser!(gotStringAsPointer, "tree.expr.str_as_ptr", "908");
