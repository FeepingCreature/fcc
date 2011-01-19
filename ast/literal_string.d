module ast.literal_string;

import ast.base, ast.literals, ast.pointer, ast.arrays;

class StringExpr : Expr, HasInfo {
  string str;
  this() { }
  this(string s) { str = s; this(); }
  mixin defaultIterate!();
  string name_used;
  void selectName(AsmFile af) {
    if (!name_used) {
      name_used = af.allocConstant(Format("string_constant_", af.constants.length), cast(ubyte[]) str);
    }
  }
  Expr getPointer() {
    return reinterpret_cast(Single!(Pointer, Single!(Char)), new LateSymbol(&selectName, &name_used)); 
  }
  override {
    string getInfo() { return "'"~toString()[1 .. $-1]~"'"; }
    StringExpr dup() { return new StringExpr(str); }
    string toString() { return '"'~str.replace("\n", "\\n")~'"'; }
    // default action: place in string segment, load address on stack
    void emitAsm(AsmFile af) {
      getPointer().emitAsm(af);
      (mkInt(str.length)).emitAsm(af);
    }
    // IType valueType() { return new StaticArray(Single!(Char), str.length); }
    IType valueType() { return Single!(Array, Single!(Char)); }
  }
}

static this() {
  mkString = delegate Expr(string s) { return new StringExpr(s); };
}

bool gotStringExpr(ref string text, out Expr ex,
  string sep = "\"", bool alreadyMatched = false)
{
  auto t2 = text;
  if (!alreadyMatched && !t2.accept(sep)) return false;
  string s;
  while (true) {
    assert(t2.length);
    // if (t2.accept(sep)) break; // eats comments in strings
    if (auto rest = t2.startsWith(sep)) { t2 = rest; break; }
    auto ch = t2.take();
    if (ch == '\\') {
      auto ch2 = t2.take();
      if (ch2 == 'n') { s ~= "\n"; }
      else if (ch2 == 'r') { s ~= "\r"; }
      else if (ch2 == 't') { s ~= "\t"; }
      else if (ch2 == 'x') {
        int h2i(char c) {
          if (c >= '0' && c <= '9') return c - '0';
          if (c >= 'a' && c <= 'f') return c - 'a';
          if (c >= 'A' && c <= 'F') return c - 'A';
          assert(false);
        }
        auto h1 = t2.take(), h2 = t2.take(); 
        s ~= h2i(h1) * 16 + h2i(h2);
      }
      else s ~= ch2;
    } else s ~= ch;
  }
  auto se = new StringExpr(s);
  text = t2; ex = se;
  return true;
}

Object gotStringLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  // "" handled in ast.stringex now.
  Expr ex;
  if (text.gotStringExpr(ex, "`", true)) {
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotStringLiteralExpr, "tree.expr.literal_string", "551", "`");

import ast.casting;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (cast(StringExpr) ex) {
      return getArrayPtr(ex);
    }
    return null;
  };
}
