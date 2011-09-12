module ast.literal_string;

import ast.base, ast.literals, ast.pointer, ast.arrays, ast.static_arrays;

static int string_counter;

class StringExpr : Expr, HasInfo {
  string str;
  this() { }
  this(string s) { str = s; this(); }
  mixin defaultIterate!();
  string name_used;
  void selectName(AsmFile af) {
    if (!name_used) {
      name_used = af.allocConstant(Format("string_constant_", string_counter ++), cast(ubyte[]) str);
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
  ubyte[] ba;
  while (true) {
    assert(t2.length);
    // if (t2.accept(sep)) break; // eats comments in strings
    if (auto rest = t2.startsWith(sep)) { t2 = rest; break; }
    byte xtake() {
      auto res = (cast(byte[]) t2)[0];
      t2 = cast(string) (cast(byte[]) t2)[1..$];
      return res;
    }
    auto ch = xtake();
    if (ch == '\\') {
      auto ch2 = xtake();
      if (ch2 == 'n') { ba ~= cast(ubyte[]) "\n"; }
      else if (ch2 == 'r') { ba ~= cast(ubyte[]) "\r"; }
      else if (ch2 == 't') { ba ~= cast(ubyte[]) "\t"; }
      else if (ch2 == 'x') {
        int h2i(char c) {
          if (c >= '0' && c <= '9') return c - '0';
          if (c >= 'a' && c <= 'f') return c - 'a' + 10;
          if (c >= 'A' && c <= 'F') return c - 'A' + 10;
          assert(false);
        }
        auto h1 = xtake(), h2 = xtake(); 
        ba ~= h2i(h1) * 16 + h2i(h2);
      }
      else ba ~= ch2;
    } else ba ~= ch;
  }
  auto se = new StringExpr(cast(string) ba);
  text = t2; ex = se;
  return true;
}

Object gotStringLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  // "" handled in ast.stringex now.
  Expr ex;
  if (text.gotStringExpr(ex, "`", true)) {
    return fastcast!(Object)~ ex;
  } else return null;
}
mixin DefaultParser!(gotStringLiteralExpr, "tree.expr.literal_string", "551", "`");

import ast.casting, ast.fold;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (resolveType(ex.valueType()) != Single!(Array, Single!(Char)))
      return null;
    if (fastcast!(StringExpr) (foldex(ex))) {
      return getArrayPtr(ex);
    }
    return null;
  };
  implicits ~= delegate Expr(Expr ex) {
    if (resolveType(ex.valueType()) != Single!(Array, Single!(Char)))
      return null;
    if (auto str = fastcast!(StringExpr) (foldex(ex))) {
      if (str.str.length == 1)
        return reinterpret_cast(Single!(Char), new DataExpr(cast(ubyte[]) str.str));
    }
    return null;
  };
}
