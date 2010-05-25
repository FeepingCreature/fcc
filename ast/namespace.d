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
  void add(T)(T t) {
    static if (is(typeof(t.sup)))
      t.sup = this;
    field ~= stuple(t.name, cast(Object) t);
  }
  typeof(field) getCheckpt() { return field; }
  void setCheckpt(typeof(field) field) { this.field = field.dup; /* prevent clobbering */ }
  Object lookup(string name) {
    foreach (entry; field)
      if (entry._0 == name) return entry._1;
    if (sup) return sup.lookup(name);
    return null;
  }
  abstract string mangle(string name, Type type);
}

T lookup(T)(Namespace ns, string name) {
  if (auto res = cast(T) ns.lookup(name)) return res;
  assert(false, "No such "~T.stringof~": "~name);
}

import tools.threads;
TLS!(Namespace) namespace;

import parseBase;
Object gotNamed(ref string text, ParseCb cont, ParseCb rest) {
  // logln("Match variable off ", text.next_text());
  string name, t2 = text;
  if (t2.gotIdentifier(name, true)) {
    retry:
    if (auto res = namespace().lookup(name)) {
      if (!text.accept(name)) throw new Exception("WTF! "~name~" at "~text.next_text());
      return res;
    }
    if (name.rfind(".") != -1) {
      name = name[0 .. name.rfind(".")]; // chop up what _may_ be members!
      goto retry;
    }
    error = "unknown identifier "~name;
  }
  return null;
}
