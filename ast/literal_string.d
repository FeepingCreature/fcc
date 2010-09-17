module ast.literal_string;

import ast.base, ast.modules, ast.literals, ast.pointer, ast.static_arrays;

class StringExpr : CValue, Setupable {
  string str;
  Module forb;
  this() { forb = current_module(); current_module().addSetupable(this); }
  this(string s) { this(); str = s; }
  mixin DefaultDup!();
  mixin defaultIterate!();
  string name_used;
  override void setup(AsmFile af) {
    if (name_used) return;
    name_used = Format("cons_", af.constants.length);
    af.constants[name_used] = cast(ubyte[]) str;
  }
  override string toString() { return '"'~str.replace("\n", "\\n")~'"'; }
  // default action: place in string segment, load address on stack
  override void emitAsm(AsmFile af) {
    assert(false, "Why are you pushing a string on the stack? This seems iffy to me. ");
  }
  override void emitLocation(AsmFile af) {
    assert(!!name_used, Format("\"", str, "\" not set up (in ", forb, " vs. ", current_module(), ")"));
    af.pushStack("$"~name_used, Single!(Pointer, Single!(Char)));
  }
  override IType valueType() { return new StaticArray(Single!(Char), str.length); }
}

static this() {
  mkString = delegate CValue(string s) { return new StringExpr(s); };
}

bool gotStringExpr(ref string text, out Expr ex, string sep = "\"") {
  auto t2 = text;
  StringExpr se;
  return t2.accept(sep) &&
    (se = new StringExpr, true) &&
    (se.str = t2.slice(sep).subst(sep), true) &&
    (text = t2, true) &&
    (ex = se, true);
}

Object gotStringLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  // "" handled in ast.stringex now.
  Expr ex;
  if (text.gotStringExpr(ex, "`")) {
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotStringLiteralExpr, "tree.expr.literal_string", "551");
