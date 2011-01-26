module ast.namespace;

import ast.base;

T aadup(T)(T t) {
  T res;
  foreach (key, value; t) res[key] = value;
  return res;
}

bool[string] reserved;
static this() {
  reserved["auto"] = true;
  reserved["return"] = true;
}

import tools.ctfe, tools.base: stuple, Format, Repeat;
import ast.int_literal, ast.float_literal;
class Namespace {
  Namespace sup;
  T get(T)() {
    auto cur = this;
    do {
      if (auto res = fastcast!(T)~ cur) return res;
    } while (null !is (cur = cur.sup));
    // throw new Exception(Format("No ", T.stringof, " above ", this, "!"));
    // logln("No ", T.stringof, " above ", this, "!");
    return null;
  }
  Stuple!(string, Object)[] field;
  Object[string] field_cache;
  void rebuildCache() {
    field_cache = null;
    foreach (entry; field) field_cache[entry._0] = entry._1;
  }
  // reverse of rebuildCache
  void rebuildField() {
    field.length = field_cache.length;
    int id;
    foreach (key, value; field_cache)
      field[id++] = stuple(key, value);
  }
  typeof(mixin(S.ctReplace("$", "(fastcast!(T)~ field[0]._1)")))[] selectMap(T, string S)() {
    int count;
    foreach (entry; field) if (fastcast!(T)~ entry._1) count++;
    alias typeof(mixin(S.ctReplace("$", "(fastcast!(T)~ field[0]._1)"))) restype;
    auto res = new restype[count];
    int i;
    foreach (entry; field)
      if (auto t = fastcast!(T)~ entry._1)
        res[i++] = mixin(S.ctReplace("$", "t"));
    return res;
  }
  void select(T)(void delegate(string, T) dg) {
    foreach (entry; field)
      if (auto t = fastcast!(T)~ entry._1)
        dg(entry._0, t);
  }
  
  const int cachepoint = 6;
  
  void __add(string name, Object obj) {
    if (name && lookup(name, true)) {
      throw new Exception(Format(
        name, " already defined in ",
        this, ": ", lookup(name)
      ));
    }
    if (field.length == cachepoint) rebuildCache;
    field ~= stuple(name, obj);
    if (field.length > cachepoint) field_cache[name] = obj;
  }
  void _add(string name, Object obj) {
    if (auto ns = fastcast!(Namespace)~ obj) {
      // if (ns.sup) asm { int 3; }
      assert(!ns.sup, Format("While adding ", obj, " to ", this, ": object already in ", ns.sup, "! "));
      ns.sup = this;
    }
    __add(name, obj);
  }
  void add(T...)(T t) {
    static if (T.length == 1) {
      alias t[0] n;
      static assert(is(typeof(n.getIdentifier()): string),
        T[0].stringof~" not named identifier and no name given. ");
      string name = n.getIdentifier();
    } else static if (T.length == 2) {
      alias t[1] n;
      string name = t[0];
    } else static assert(false, "wtfux");
    _add(name, fastcast!(Object)~ n);
  }
  typeof(field) getCheckpt() { return field; }
  void setCheckpt(typeof(field) field) { this.field = field.dup; rebuildCache(); /* prevent clobbering */ }
  Object lookup(string name, bool local = false) {
    if (name in reserved) return null;
    { int temp; if (name.gotInt(temp)) return null; }
    { float temp; if (name.gotFloat(temp)) return null; }
    if (field.length > cachepoint) {
      if (auto p = name in field_cache) return *p;
    } else {
      foreach (entry; field) if (entry._0 == name) return entry._1;
    }
    if (!local && sup) return sup.lookup(name, local);
    return null;
  }
  abstract string mangle(string name, IType type);
  abstract Stuple!(IType, string, int)[] stackframe();
}

class NoNameSpace : Namespace {
  override string mangle(string name, IType type) { assert(false); }
  override Stuple!(IType, string, int)[] stackframe() { assert(false); }
}

interface RelNamespace {
  Object lookupRel(string str, Expr base);
  bool isTempNamespace(); // temporary namespace - not an error if lookup fails
}

interface SemiRelNamespace {
  RelNamespace resolve();
}

// applies whenever the base ptr parameter is different from "namespace*"; ie. classref.
interface RelNamespaceFixupBase : RelNamespace {
  IType genCtxType(RelNamespace context);
}

T lookup(T)(Namespace ns, string name) {
  if (auto res = fastcast!(T)~ ns.lookup(name)) return res;
  assert(false, "No such "~T.stringof~": "~name);
}

import tools.threads;
TLS!(Namespace) namespace;

import parseBase, tools.log;
Object gotNamed(ref string text, ParseCb cont, ParseCb rest) {
  string name, t2 = text;
  if (t2.gotIdentifier(name, true)) {
    retry:
    if (auto res = namespace().lookup(name)) {
      if (fastcast!(IType)~ res) return null; // Positively NOT an expr.
      if (!text.accept(name))
        text.failparse("WTF ", name);
      return res;
    } else {
      // logln("No ", name, " in ", namespace());
    }
    int dotpos = name.rfind("."), dashpos = name.rfind("-");
    if (dotpos != -1 && dashpos != -1)
      if (dotpos > dashpos) goto checkDot;
      else goto checkDash;
    
    checkDash:
    if (t2.eatDash(name)) goto retry;
    
    checkDot:
    if (dotpos != -1) {
      name = name[0 .. dotpos]; // chop up what _may_ be members!
      goto retry;
    }
    
    t2.setError("unknown identifier: '", name, "'");
  }
  return null;
}

extern(C) Namespace __getSysmod();

class MiniNamespace : Namespace, ScopeLike, Named {
  string id;
  this(string id) { this.id = id; }
  override string getIdentifier() { return id; }
  override string mangle(string name, IType type) {
    if (type) return id~"_"~name~"_of_"~type.mangle();
    else return id~"_"~name;
  }
  override Stuple!(IType, string, int)[] stackframe() {
    assert(false); // wtfux.
  }
  bool internalMode;
  override string toString() { return Format("mini[", id, "] <- ", sup); }
  override void _add(string name, Object obj) {
    if (sup && !internalMode) sup._add(name, obj);
    else if (internalMode) super.__add(name, obj);
    else super._add(name, obj);
  }
  int fs = -1, fs2;
  override int framesize() {
    if (fs != -1) return fs;
    if (auto sl = fastcast!(ScopeLike)~ sup) {
      if (fs2) return fs2 + sl.framesize();
      else return sl.framesize();
    } else {
      // logln("no metric for framesize of ", id);
      if (id == "onUsing") asm { int 3; }
      throw new Exception(Format("No metric for framesize of ", id, ": sup is ", sup, "."));
    }
  }
  override Object lookup(string name, bool local = false) {
    auto res = super.lookup(name, local);
    if (!res && !local) {
      auto sysmod = __getSysmod();
      if (sysmod) res = sysmod.lookup(name, local);
    }
    // logln("mini lookup ", name, " => ", res);
    return res;
  }
}

// internal miniparse wrapper
float[string] bench;
import tools.time, ast.fold;
const bool canFail = false;
template iparse(R, string id, string rule, bool mustParse = true) {
  R iparse(T...)(string text, T _t) {
    auto start = sec();
    scope(exit) bench[id] += sec() - start;
    pushCache();
    scope(exit) popCache();
    
    static if (is(T[$-1] == AsmFile)) alias T[0 .. $-1] T2;
    else alias T T2;
    
    static if (T2.length && is(T2[0]: Namespace)) alias T2[1 .. $] T3;
    else alias T2 T3;
    
    static if (T3.length && is(T3[0]: int)) alias T3[1 .. $] T4;
    else alias T3 T4;
    
    static assert(T4.length % 2 == 0);
    
    auto myns = new MiniNamespace(id);
    
    auto backup = namespace();
    namespace.set(myns);
    scope(exit) {
      namespace.set(backup);
    }
    static if (T2.length && is(T2[0]: Namespace)) {
      myns.sup = _t[0];
      static if (T2.length > 1 && is(T2[1]: int)) {
        myns.fs2 = _t[1];
        auto t = _t[2 .. $];
      } else {
        auto t = _t[1 .. $];
      }
    } else {
      auto t = _t;
    }
    
    myns.internalMode = true;
    // compile-time for loop LALZ
    foreach (i, bogus; T4[0 .. $/2]) {
      myns.add(t[i*2], t[i*2+1]);
    }
    
    static if (is(T[$-1] == AsmFile)) {
      myns.fs = t[$-1].currentStackDepth;
    }
    
    myns.internalMode = false;
    
    sourcefiles["<internal:"~id~">"] = text;
    
    auto res = parsecon.parse(text, rule);
    auto rc = cast(R) res;
    static if (mustParse) {
      if (text.mystripl().length) text.failparse("Unknown text: '"~text~"'");
      if (!res)                text.failparse("Failed to parse");
      if (!rc)                 text.failparse("Wrong result type: wanted ", R.stringof, ", got ", res);
    } else {
      if (text.length || !rc) return null;
    }
    opt(rc);
    return rc;
  }
}

Object gotNamedType(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    retry:
    if (auto type = fastcast!(IType)~ namespace().lookup(id)) {
      text = t2;
      return fastcast!(Object)~ type;
    } else if (t2.eatDash(id)) goto retry;
  }
  return null;
}
mixin DefaultParser!(gotNamedType, "type.named", "4");

class LengthOverride : Namespace {
  Expr len;
  this(Namespace sup, Expr ex) { this.sup = sup; len = ex; }
  override {
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() { return sup.stackframe(); }
    Object lookup(string name, bool local = false) {
      if (name == "$") return fastcast!(Object)~ len;
      return sup.lookup(name, local);
    }
  }
}
