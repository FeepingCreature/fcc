module ast.namespace;

import ast.types, ast.fun, ast.variable, ast.structure;

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
  template Kind(T, string Name) {
    mixin(`
      Stuple!(string, T)[] $NAMEfield;
      void add$NAME(T t) {
        static if (is(typeof(t.sup)))
          t.sup = this;
        $NAMEfield ~= stuple(t.name, t);
      }
      Stuple!(string, T)[] $NAMEGetCheckpt() { return $NAMEfield; }
      void $NAMESetCheckpt(Stuple!(string, T)[] field) { $NAMEfield = field.dup; /* prevent clobbering */ }
      T lookup$NAME(string name) {
        // logln("Lookup ", name, " as $NAME in ", $NAMEfield);
        foreach (entry; $NAMEfield)
          if (entry._0 == name) return entry._1;
        if (sup) return sup.lookup$NAME(name);
        return null;
      }
    `.ctReplace("$NAME", Name));
  }
  template _Kinds(T...) {
    mixin Kind!(T[0], T[1]);
    static if (T.length > 2) mixin _Kinds!(T[2 .. $]);
  }
  template Kinds(T...) {
    mixin _Kinds!(T);
    Object lookup(string name) {
      foreach (i, bogus; Repeat!(void, T.length / 2)) {
        mixin(`
          foreach (entry; $NAMEfield)
            if (entry._0 == name) return cast(Object) entry._1;
          `.ctReplace("$NAME", T[2*i+1])
        );
      }
      if (sup) return sup.lookup(name);
      return null;
    }
  }
  mixin Kinds!(Class, "Class", Structure, "Struct", Function, "Fun", Variable, "Var");
  abstract string mangle(string name, Type type);
}

Function lookupFun(Namespace ns, string name) {
  if (auto res = ns.lookupFun(name)) return res;
  assert(false, "No such function identifier: "~name);
}

Class lookupClass(Namespace ns, string name) {
  if (auto res = ns.lookupClass(name)) return res;
  assert(false, "No such class identifier: "~name);
}

Structure lookupStruct(Namespace ns, string name) {
  if (auto res = ns.lookupStruct(name)) return res;
  assert(false, "No such struct identifier: "~name);
}

Variable lookupVar(Namespace ns, string name) {
  if (auto res = ns.lookupVar(name)) return res;
  assert(false, "No such variable identifier: "~name);
}
