module ast.enums;

import parseBase;
import ast.base, ast.types, ast.namespace, ast.casting, ast.math, ast.opers;

class Enum : Namespace, IType, Named, ExprLikeThingy {
  string name;
  IType base;
  this(string n, IType b) {
    name = n;
    base = b;
    sup = namespace();
  }
  // members
  string[] names;
  Expr[] values;
  void addEntry(string s, Expr e) { names ~= s; values ~= e; }
  override {
    string getIdentifier() { return name; }
    int size() { return base.size(); }
    string mangle() { return "enum_"~name; }
    ubyte[] initval() { return base.initval; }
    bool isPointerLess() { return base.isPointerLess(); }
    bool isComplete() { return true; }
    mixin TypeDefaults!(false, true);
    Object lookup(string name, bool local = false) {
      foreach (i, n; names)
        if (n == name)
          return fastcast!(Object) (reinterpret_cast(this, values[i]));
      if (local) return null;
      return sup.lookup(name, local);
    }
    string mangle(string name, IType type) {
      fail; // what are you DOING
      return null;
    }
    Stuple!(IType, string, int)[] stackframe() {
      fail; // AAAAAAHHH STOP IIT
      return null;
    }
  }
}

import ast.int_literal;

Object gotEnum(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!t2.gotIdentifier(name))
    t2.failparse("Enum name expected! ");
  IType base = Single!(SysInt);
  if (t2.accept(":")) {
    if (!rest(t2, "type", &base))
      t2.failparse("Expected enum base type! ");
  }
  if (!t2.accept("{"))
    t2.failparse("Expected opening bracket for enum. ");
  auto en = new Enum(name, base);
  
  auto backup = namespace();
  namespace.set(en);
  scope(exit) namespace.set(backup);
  
  Expr val, one;
  if (base == Single!(Short)) {
    val = new IntLiteralAsShort(mkInt(0));
    one = new IntLiteralAsShort(mkInt(1));
  } else if (base == Single!(Byte)) {
    val = new ShortAsByte(new IntLiteralAsShort(mkInt(0)));
    one = new ShortAsByte(new IntLiteralAsShort(mkInt(1)));
  } else {
    val = mkInt(0);
    one = mkInt(1);
  }
  
grabIdentifier:
  string idname;
  if (!t2.gotIdentifier(idname))
    t2.failparse("Expected enum member identifier");
  if (t2.accept("=")) {
    if (!rest(t2, "tree.expr", &val))
      t2.failparse("Expected enum value expr");
    auto backupval = val;
    if (!gotImplicitCast(val, (IType it) { return test(it == base); }))
      t2.failparse("Enum value of ", backupval.valueType(), " did not match ",
                    base);
  } else {
    val = lookupOp("+", val, one);
  }
  en.addEntry(idname, val);
  if (t2.accept(",")) goto grabIdentifier;
  // end goto
  if (!t2.accept("}"))
    t2.failparse("Expected closing bracket");
  text = t2;
  en.sup.add(en);
  return Single!(NoOp);
}
mixin DefaultParser!(gotEnum, "tree.toplevel.enum", null, "enum");

// enums cast implicitly to their base type
// this can be useful when wrapping APIs
// that define enum members in relation to other members
// ie. A = 5, B = A + 4
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto vt = ex.valueType();
    auto en = fastcast!(Enum) (vt);
    if (!en) return null;
    if (auto lv = fastcast!(LValue) (ex))
      return new RCC(en.base, lv);
    return reinterpret_cast(en.base, ex);
  };
}
