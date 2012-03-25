module ast.namespace;

import ast.base;

T aadup(T)(T t) {
  T res;
  foreach (key, value; t) res[key] = value;
  return res;
}

class AlreadyDefinedException : Exception {
  this(string mesg) {
    super("AlreadyDefinedException: "~mesg);
    // fail;
  }
}

// This is intended to be used for function overload sets.
interface Extensible {
  // create compound object of this and obj.
  Extensible extend(Extensible ex);
  // if the collection contains only one object, return that; otherwise null
  Extensible simplify();
}

struct NSCache(T...) {
  int hash;
  static if (T.length == 1)
    T[0][] field;
  else
    Stuple!(T)[] field;
}

struct PreallocatedField(int StaticSize, T) {
  int length;
  T[StaticSize] static_;
  T[][] dynamics_;
  int opApply(int delegate(ref T t) dg) {
    outer:for (int i = 0; i < length; ++i) {
      if (i < static_.length) {
        if (auto res = dg(static_[i])) return res;
      } else {
        int j = i - StaticSize;
        foreach (field; dynamics_) {
          if (j < field.length) {
            if (auto res = dg(field[j])) return res;
            else continue outer;
          }
          j -= field.length;
        }
        logln("Length ", length, " excessive due to ", StaticSize, ", ", dynamics_ /map/ ex!("f -> f.length"));
        fail;
      }
    }
    return 0;
  }
  string toString() {
    string res = Format("PF[", length, "/", StaticSize, ": ");
    bool first;
    foreach (entry; *this) {
      if (first) first = false;
      else res ~= ", ";
      res ~= Format(entry);
    }
    return res ~ "]";
  }
  void opCatAssign(ref T t) {
    scope(success) length++;
    if (length < StaticSize) {
      static_[this.length] = t;
    } else {
      int len2 = length - StaticSize;
      foreach (field; dynamics_) {
        if (len2 < field.length) {
          field[len2] = t;
          return;
        }
        len2 -= field.length;
      }
      auto newsize = 1 << dynamics_.length;
      dynamics_ ~= new T[newsize];
      dynamics_[$-1][0] = t;
    }
  }
  T opIndex(int i) {
    if (i < static_.length) return static_[i];
    else {
      int j = i - StaticSize;
      foreach (field; dynamics_) {
        if (j < field.length) {
          return field[j];
        }
        j -= field.length;
      }
      fail;
    }
  }
  PreallocatedField dup() {
    PreallocatedField res = void;
    res.length = length;
    
    res.dynamics_ = null;
    if (length > StaticSize) { // compress
      res.dynamics_.length = 1;
      res.dynamics_[0] = new T[this.length - StaticSize];
    }
    
    int i;
    foreach (ref value; *this) {
      int j = i - StaticSize;
      if (i < static_.length)
        res.static_[i] = value;
      else
        res.dynamics_[0][j] = value;
      i++;
    }
    
    return res;
  }
}

import tools.ctfe, tools.base: stuple, Format, Repeat, ex;
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
  // empirically determined: the overwhelming majority of namespaces contain less than 7 entries
  PreallocatedField!(7, Stuple!(string, Object)) field;
  int max_field_size;
  Object[string] field_cache;
  int mod_hash;
  void rebuildCache() {
    field_cache = null;
    foreach (entry; field) field_cache[entry._0] = entry._1;
    mod_hash ++;
  }
  typeof(mixin(S.ctReplace("$", "(fastcast!(T)~ field[0]._1)")))[] selectMap(T, string S)(NSCache!(typeof(mixin(S.ctReplace("$", "(fastcast!(T)~ field[0]._1)"))))* cachep = null) {
    if (cachep && cachep.hash == mod_hash) return cachep.field;
    int count;
    foreach (entry; field) if (fastcast!(T)~ entry._1) count++;
    alias typeof(mixin(S.ctReplace("$", "(fastcast!(T)~ field[0]._1)"))) restype;
    auto res = new restype[count];
    int i;
    foreach (entry; field)
      if (auto t = fastcast!(T)~ entry._1)
        res[i++] = mixin(S.ctReplace("$", "t"));
    if (cachep) { cachep.hash = mod_hash; cachep.field = res; }
    return res;
  }
  void select(T)(void delegate(string, T) dg, NSCache!(string, T)* cachep = null) {
    if (cachep) {
      if (cachep.hash != mod_hash) {
        int i;
        foreach (entry; field)
          if (auto t = fastcast!(T) (entry._1)) {
            auto data = stuple(entry._0, t);
            if (i < cachep.field.length) cachep.field[i++] = data;
            else { i++; cachep.field ~= data; }
          }
        cachep.field = cachep.field[0..i];
        cachep.hash = mod_hash;
      }
      foreach (entry; cachep.field)
        dg(entry._0, entry._1);
    } else {
      foreach (entry; field)
        if (auto t = fastcast!(T) (entry._1))
          dg(entry._0, t);
    }
  }
  
  const int cachepoint = 6;
  
  void __add(string name, Object obj) {
    if (name) {
      if (auto thing = lookup(name, true)) {
        // logln(name, " in ", this, "(local) => ", thing);
        if (auto et = fastcast!(Extensible) (thing)) {
          auto eo = fastcast!(Extensible) (obj);
          if (!eo) {
            logln("Tried to overload ", name, " (", thing, ")", ", but ", obj, " is not extensible!");
            fail;
          }
          bool found;
          foreach (ref entry; field) {
            if (entry._1 is thing) {
              assert(entry._0 == name);
              entry._1 = fastcast!(Object) (et.extend(eo));
              found = true;
              break;
            }
          }
          if (!found) throw new Exception(Format(
            "Tried to overload ", thing, " with ",
            obj, " @", this, " but it's not in the field! "
          ));
          if (field.length > cachepoint) rebuildCache;
          return;
        }
        if (auto named = fastcast!(Named) (thing)) {
          auto ident = named.getIdentifier();
          auto tup = lookupPos(ident);
          auto row = tup._0, col = tup._1, file = tup._2;
          throw new AlreadyDefinedException(Format(
            "'", name, "' already defined\n",
            file, ":", row, ":", col, ": previously defined here"
          ));
        }
        throw new AlreadyDefinedException(Format(
          "'", name, "' already defined in ",
          this, ": ", lookup(name)
        ));
      }
    }
    if (field.length == cachepoint) rebuildCache;
    field ~= stuple(name, obj);
    max_field_size = max(max_field_size, field.length);
    if (field.length > cachepoint) field_cache[name] = obj;
    mod_hash ++;
  }
  void _add(string name, Object obj) {
    if (auto ns = fastcast!(Namespace)~ obj) {
      if (ns.sup && ns.sup !is this) {
        logln("While adding ", obj, " to ", this, ": object already in ", ns.sup, "! ");
        fail;
      }
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
    debug { int temp; if (name.gotInt(temp)) fail; }
    debug { float temp; if (name.gotFloat(temp)) fail; }
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

interface ExprLikeThingy { }

extern(C) Namespace __getSysmod();

class MiniNamespace : Namespace, ScopeLike, Named {
  string id;
  this(string id) { this.id = id; }
  bool internalMode;
  int fs = -1, fs2;
  override {
    string getIdentifier() { return id; }
    string mangle(string name, IType type) {
      if (type) return id~"_"~name~"_of_"~type.mangle();
      else return id~"_"~name;
    }
    Stuple!(IType, string, int)[] stackframe() {
      assert(false); // wtfux.
    }
    mixin DefaultScopeLikeGuards!();
    string toString() { return Format("mini[", id, "](", framesize(), ") <- ", sup); }
    void _add(string name, Object obj) {
      if (sup && !internalMode) sup._add(name, obj);
      else super.__add(name, obj);
    }
    int framesize() {
      if (fs != -1) return fs;
      if (auto sl = fastcast!(ScopeLike)~ sup) {
        auto supsz = sl.framesize();
        if (supsz == -1) return -1;
        if (fs2) return fs2 + supsz;
        else return supsz;
      } else {
        return -1;
        // throw new Exception(Format("No metric for framesize of ", id, ": sup is ", sup, "."));
      }
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, local);
      if (!res && !local) {
        auto sysmod = __getSysmod();
        if (sysmod) res = sysmod.lookup(name, local);
      }
      // logln("mini lookup ", name, " => ", res);
      return res;
    }
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
    bool allInternal;
    static if (T2.length && is(T2[0]: Namespace)) {
      myns.sup = _t[0];
      static if (T2.length > 1 && is(T2[1] == bool)) {
        allInternal = _t[1];
        auto t = _t[2 .. $];
      } else static if (T2.length > 1 && is(T2[1]: int)) {
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
    
    myns.internalMode = allInternal;
    
    sourcefiles["<internal:"~id~">"] = text;
    
    auto res = parsecon.parse(text, rule);
    auto rc = fastcast!(R) (res);
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
  if (t2.gotIdentifier(id, true)) {
    retry:
    if (auto type = fastcast!(IType) (namespace().lookup(id))) {
      text = t2;
      return fastcast!(Object) (forcedConvert(type));
    }
    else if (t2.eatDash(id)) goto retry;
    else if (t2.eatDot(id)) goto retry;
  }
  return null;
}
mixin DefaultParser!(gotNamedType, "type.named", "4");

class LengthOverride : Namespace, ScopeLike {
  Expr len;
  this(Namespace sup, Expr ex) { this.sup = sup; len = ex; }
  override {
    int framesize() { return sup.get!(ScopeLike).framesize(); }
    Statement[] getGuards() { return sup.get!(ScopeLike).getGuards(); }
    int[] getGuardOffsets() { return sup.get!(ScopeLike).getGuardOffsets(); }
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string, int)[] stackframe() { return sup.stackframe(); }
    string toString() { return Format("[$ = ", len, "] <- ", sup); }
    Object lookup(string name, bool local = false) {
      if (name == "$") return fastcast!(Object)~ len;
      return sup.lookup(name, local);
    }
  }
}

bool* getPtrResizing(ref bool[] array, int offs) {
  if (array.length <= offs) array.length = offs + 1;
  return &array[offs];
}

interface Importer {
  Namespace[] getImports();
  void checkImportsUsage();
  Namespace[]* getImportsPtr(ImportType);
  Object lookupInImports(string name, bool local);
}

extern(C) void check_imports_usage(string info, Namespace[] imports, bool[] importsUsed);
template ImporterImpl() {
  Namespace[] imports, public_imports, static_imports;
  Namespace[] getImports() { return imports ~ public_imports ~ static_imports; }
  bool[] importsUsed; // print warnings on unused imports (but NOT public ones!)
  Namespace[]* getImportsPtr(ImportType type) {
    switch (type) {
      case ImportType.Regular: return &imports;
      case ImportType.Public: return &public_imports;
      case ImportType.Static: return &static_imports;
    }
  }
  void checkImportsUsage() { check_imports_usage(name, imports, importsUsed); }
  Object lookupInImports(string name, bool local) {
    Object res;
    void addres(Object obj) {
      if (!res) { res = obj; return; }
      auto ex = fastcast!(Extensible) (res), ex2 = fastcast!(Extensible)(obj);
      if (ex && !ex2 || !ex && ex2) {
        throw new Exception(Format("While looking up ", name, ": ambiguity between ",
          res, " and ", obj, ": one is overloadable and the other isn't"));
      }
      if (!ex) return;
      res = fastcast!(Object) (ex.extend(ex2));
    }
    void finalize() {
      auto xt = fastcast!(Extensible) (res);
      if (!xt) return;
      if (auto simp = xt.simplify()) res = fastcast!(Object) (simp);
    }
    
    foreach (ns; public_imports) {
      if (auto res = ns.lookup(name, true)) {
        addres(res);
      }
    }
    
    foreach (ns; static_imports) if (auto imod = fastcast!(IModule) (ns)) {
      if (auto lname = name.startsWith(imod.getIdentifier()).startsWith(".")) {
        if (auto res = ns.lookup(lname)) return res;
      }
    }
    
    if (local) { finalize; return res; }
    
    foreach (i, ns; imports) {
      if (auto res = ns.lookup(name, true)) {
        *getPtrResizing(importsUsed, i) = true;
        addres(res);
      }
    }
    
    if (sysmod && sysmod !is this && name != "std.c.setjmp")
      if (auto res = sysmod.lookup(name, true))
        addres(res);
    
    finalize;
    return res;
  }
}

abstract class NamespaceImporter : Namespace, Importer {
}

NamespaceImporter sysmod;
