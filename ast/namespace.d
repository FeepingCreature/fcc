module ast.namespace;

import ast.base;

T aadup(T)(T t) {
  T res;
  foreach (key, value; t) res[key] = value;
  return res;
}

import tools.ctfe, tools.base: stuple, Format, Repeat;
class Namespace {
  Namespace sup;
  T get(T)() {
    auto cur = this;
    do {
      if (auto res = cast(T) cur) return res;
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
  void select(T)(void delegate(string, T) dg) {
    foreach (entry; field)
      if (auto t = cast(T) entry._1)
        dg(entry._0, t);
  }
  void __add(string name, Object obj) {
    if (name && lookup(name, true)) {
      throw new Exception(Format(
        name, " already defined in ",
        this, ": ", lookup(name)
      ));
    }
    field ~= stuple(name, obj);
    field_cache[name] = obj;
  }
  void _add(string name, Object obj) {
    if (auto ns = cast(Namespace) obj) {
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
    _add(name, cast(Object) n);
  }
  typeof(field) getCheckpt() { return field; }
  void setCheckpt(typeof(field) field) { this.field = field.dup; rebuildCache(); /* prevent clobbering */ }
  Object lookup(string name, bool local = false) {
    if (auto p = name in field_cache) return *p;
    if (!local && sup) return sup.lookup(name, local);
    return null;
  }
  abstract string mangle(string name, IType type);
  abstract Stuple!(IType, string, int)[] stackframe();
}

interface RelNamespace {
  Object lookupRel(string str, Expr base);
}

interface SemiRelNamespace {
  RelNamespace resolve();
}

// applies whenever the base ptr parameter is different from "namespace*"; ie. classref.
interface RelNamespaceFixupBase : RelNamespace {
  IType genCtxType(RelNamespace context);
}

T lookup(T)(Namespace ns, string name) {
  if (auto res = cast(T) ns.lookup(name)) return res;
  assert(false, "No such "~T.stringof~": "~name);
}

import tools.threads;
TLS!(Namespace) namespace;

import parseBase, tools.log;
Object gotNamed(ref string text, ParseCb cont, ParseCb rest) {
  string name, t2 = text;
  // Yes, special handling. Don't like it? Don't care.
  bool special;
  if (t2.accept("invoke-exit")) name = "_invokeExit";
  else if (t2.accept("raise-signal")) name = "_signalHandler";
  else if (t2.accept("raise-error")) name = "_signalErrorHandler";
  if (name) special = true;
  if (special || t2.gotIdentifier(name, true)) {
    retry:
    if (auto res = namespace().lookup(name)) {
      if (special) {
        text = t2;
      } else {
        if (!text.accept(name)) throw new Exception("WTF! "~name~" at "~text.next_text());
      }
      return res;
    } else {
      // logln("No ", name, " in ", namespace());
    }
    if (name.rfind(".") != -1) {
      name = name[0 .. name.rfind(".")]; // chop up what _may_ be members!
      goto retry;
    }
    error = "unknown identifier "~name~". ";
  }
  return null;
}

extern(C) Namespace __getSysmod();

class MiniNamespace : Namespace, ScopeLike {
  string id;
  this(string id) { this.id = id; }
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
    if (auto sl = cast(ScopeLike) sup) {
      if (fs2) return fs2 + sl.framesize();
      else return sl.framesize();
    } else {
      logln("no metric for framesize of ", id);
      assert(false);
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
import tools.time;
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
    
    auto res = parsecon.parse(text, rule);
    auto rc = cast(R) res;
    static if (mustParse) {
      if (text.length) throw new Exception(Format("Unknown text in ", id, ": ", text));
      if (!res)        throw new Exception(Format("Failed to parse ", id, " at ", text.next_text()));
      if (!rc)         throw new Exception(Format("Wrong result type in ", id, ": wanted ", R.stringof, "; got ", res));
    } else {
      if (text.length || !rc) return null;
    }
    return rc;
  }
}

Object gotNamedType(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    if (auto type = cast(IType) namespace().lookup(id)) {
      text = t2;
      return cast(Object) type;
    }
  }
  return null;
}
mixin DefaultParser!(gotNamedType, "type.named", "4");
