module ast.namespace;

import ast.base;

import tools.ctfe, tools.base: stuple, Format, Repeat;
class Namespace {
  Namespace sup;
  T get(T)() {
    auto cur = this;
    do {
      if (auto res = cast(T) cur) return res;
    } while (null !is (cur = cur.sup));
    throw new Exception(Format("No ", T.stringof, " above ", this, "!"));
  }
  Stuple!(string, Object)[] field;
  void select(T)(void delegate(string, T) dg) {
    foreach (entry; field)
      if (auto t = cast(T) entry._1)
        dg(entry._0, t);
  }
  void _add(string name, Object obj) {
    if (lookup(name, true)) {
      throw new Exception(Format(
        name, " already defined in ",
        this, ": ", lookup(name)
      ));
    }
    if (auto ns = cast(Namespace) obj)
      ns.sup = this;
    field ~= stuple(name, obj);
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
  void setCheckpt(typeof(field) field) { this.field = field.dup; /* prevent clobbering */ }
  Object lookup(string name, bool local = false) {
    foreach (entry; field) {
      if (entry._0 == name) return entry._1;
    }
    if (!local && sup) return sup.lookup(name, local);
    return null;
  }
  abstract string mangle(string name, IType type);
  abstract Stuple!(IType, string, int)[] stackframe();
}

interface RelNamespace {
  Object lookupRel(string str, Expr base);
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
  if (t2.gotIdentifier(name, true)) {
    retry:
    if (auto res = namespace().lookup(name)) {
      if (!text.accept(name)) throw new Exception("WTF! "~name~" at "~text.next_text());
      return res;
    } else {
      // logln("No ", name, " in ", namespace());
    }
    if (name.rfind(".") != -1) {
      name = name[0 .. name.rfind(".")]; // chop up what _may_ be members!
      goto retry;
    }
    error = "unknown identifier "~name;
  }
  return null;
}

class MiniNamespace : Namespace {
  string id;
  this(string id) { this.id = id; }
  override string mangle(string name, IType type) {
    return id~"_"~name~"_of_"~type.mangle();
  }
  override Stuple!(IType, string, int)[] stackframe() {
    assert(false); // wtfux.
  }
}

// internal miniparse wrapper
template iparse(R, string id, string rule) {
  R iparse(T...)(string text, T t) {
    text = text.dup; // circumvent the memoizer TODO: Better way?
    static assert(T.length % 2 == 0);
    auto myns = new MiniNamespace(id);
    // compile-time for loop LALZ
    foreach (i, bogus; T[0 .. $/2]) {
      myns.add(t[i*2], t[i*2+1]);
    }
    auto backup = namespace();
    namespace.set(myns);
    scope(exit) namespace.set(backup);
    return cast(R) parsecon.parse(text, rule);
  }
}
