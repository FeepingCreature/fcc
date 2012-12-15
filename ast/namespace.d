module ast.namespace;

import ast.base;
import tools.base, tools.functional;

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
  void clean() {
    dynamics_ = null;
    length = 0;
  }
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
        logln("Length "[], length, " excessive due to "[], StaticSize, ", "[], dynamics_ /map/ ex!("f -> f.length"[]));
        fail;
      }
    }
    return 0;
  }
  string toString() {
    string res = Format("PF["[], length, "/"[], StaticSize, ": "[]);
    bool first = true;
    foreach (entry; *this) {
      if (first) first = false;
      else res ~= ", ";
      res ~= qformat(entry._0, ": ", entry._1);
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

import tools.ctfe, tools.base: stuple, Format, Repeat, ex, TTTuple=Tuple;
import ast.int_literal, ast.float_literal;
class Namespace {
  Namespace sup;
  T get(T)() {
    auto cur = this;
    do {
      if (auto res = fastcast!(T)~ cur) return res;
    } while (null !is (cur = cur.sup));
    // throw new Exception(Format("No "[], T.stringof, " above "[], this, "!"[]));
    // logln("No "[], T.stringof, " above "[], this, "!"[]);
    return null;
  }
  // benched to be optimal; the overwhelming majority of namespaces contain less than 7 entries
  PreallocatedField!(6, Stuple!(string, Object)) field;
  int max_field_size;
  Object[string] field_cache;
  int mod_hash;
  void rebuildCache() {
    field_cache = null;
    foreach (entry; field) field_cache[entry._0] = entry._1;
    mod_hash ++;
  }
  typeof(mixin(S.ctReplace("$"[], "(fastcast!(T)~ field[0]._1)"[])))[] selectMap(T, string S)(NSCache!(typeof(mixin(S.ctReplace("$"[], "(fastcast!(T)~ field[0]._1)"[]))))* cachep = null) {
    if (cachep && cachep.hash == mod_hash) return cachep.field;
    int count;
    foreach (entry; field) if (fastcast!(T)~ entry._1) count++;
    alias typeof(mixin(S.ctReplace("$"[], "(fastcast!(T)~ field[0]._1)"[]))) restype;
    auto res = new restype[count];
    int i;
    foreach (entry; field)
      if (auto t = fastcast!(T)~ entry._1)
        res[i++] = mixin(S.ctReplace("$"[], "t"[]));
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
      // don't do lookup(name, true) because that matches stuff like public imports also!
      // only try to overload truly local funs
      if (auto thing = lookupInField(name)) {
        if (auto et = fastcast!(Extensible) (thing)) {
          auto eo = fastcast!(Extensible) (obj);
          if (!eo) {
            logln("Tried to overload "[], name, " ("[], thing, ")", "[], but "[], obj, " is not extensible!"[]);
            fail;
          }
          bool found;
          foreach (ref entry; field) {
            // check name too, because we might have added that thing before via alias
            if (entry._1 is thing && entry._0 == name) {
              entry._1 = fastcast!(Object) (et.extend(eo));
              if (!entry._1) {
                logln("add failure: ", name, " and ", et);
                fail;
              }
              found = true;
              break;
            }
          }
          if (!found) throw new Exception(Format(
            "Tried to overload "[], thing, " with "[],
            obj, " @"[], this, " but it's not in the field! "
          ));
          if (field.length > cachepoint) rebuildCache;
          return;
        }
        breakpoint;
        if (auto named = fastcast!(Named) (thing)) {
          auto ident = named.getIdentifier();
          auto tup = lookupPos(ident);
          auto row = tup._0, col = tup._1, file = tup._2;
          if (row || col) {
            throw new AlreadyDefinedException(Format(
              "'"[], name, "' already defined\n"[],
              file, ":"[], row, ":"[], col, ": previously defined here"
            ));
          }
        }
        throw new AlreadyDefinedException(Format(
          "'"[], name, "' already defined in "[],
          this, ": "[], lookup(name)
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
        logln("While adding "[], obj, " to "[], this, ": object already in "[], ns.sup, "! "[]);
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
        T[0].stringof~" not named identifier and no name given. "[]);
      string name = n.getIdentifier();
    } else static if (T.length == 2) {
      alias t[1] n;
      string name = t[0];
    } else static assert(false, "wtfux"[]);
    _add(name, fastcast!(Object)~ n);
  }
  typeof(field) getCheckpt() { return field; }
  void setCheckpt(typeof(field) field) {
    this.field = field.dup;
    rebuildCache(); /* prevent clobbering */
  }
  Object lookupInField(string name) {
    if (field.length > cachepoint) {
      if (auto p = name in field_cache) return *p;
    } else {
      foreach (entry; field) if (faststreq(entry._0, name)) return entry._1;
    }
    return null;
  }
  Object[string] supcache;
  Object lookup(string name, bool local = false) {
    if (name in reserved) return null;
    debug { int temp; if (name.gotInt(temp)) fail; }
    debug { float temp; if (name.gotFloat(temp)) fail; }
    if (auto res = lookupInField(name)) return res;
    if (!local && sup) {
      if (auto p = name in supcache) return *p;
      auto res = sup.lookup(name, false);
      supcache[name] = res;
      // logln(" => ", supcache.length, " ", name);
      return res;
    }
    return null;
  }
  abstract string mangle(string name, IType type);
}

class NoNameSpace : Namespace {
  override string mangle(string name, IType type) { assert(false); }
}

interface RelNamespace {
  Object lookupRel(string str, Expr base, bool isDirectLookup = true);
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

extern(C) Stuple!(IType, string)[] _mns_stackframe(Namespace sup, typeof(Namespace.field));

class MiniNamespace : Namespace, ScopeLike, Named {
  string id;
  this(string id) { this.id = id; }
  bool internalMode;
  override {
    string getIdentifier() { return id; }
    string mangle(string name, IType type) {
      auto clean_id = id.replace("!", "").replace(" ", "_");
      if (type) return clean_id~"_"~name~"_of_"~type.mangle();
      else return clean_id~"_"~name;
    }
    Stuple!(IType, string)[] stackframe() {
      return _mns_stackframe(sup, field);
    }
    mixin DefaultScopeLikeGuards!();
    string toString() { return qformat("mini[", id, "](", stackframe().length, ") <- ", sup); }
    void _add(string name, Object obj) {
      if (sup && !internalMode) sup._add(name, obj);
      else super.__add(name, obj);
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, local);
      if (!res && !local) {
        auto sysmod = __getSysmod();
        if (sysmod) res = sysmod.lookup(name, local);
      }
      if (!res && sup) res = sup.lookup(name, local);
      // logln("mini lookup "[], name, " => "[], res);
      return res;
    }
  }
}

// internal miniparse wrapper
float[string] bench;
import tools.time, ast.fold;
const bool canFail = false;
alias TTTuple!(true, false) dontopt;
template iparse(R, string id, string rule, bool mustParse = true, bool optres = true) {
  R iparse(T...)(string text, T _t) {
    auto start = sec();
    scope(exit) bench[id] += sec() - start;
    auto popCache = pushCache(); scope(exit) popCache();
    
    static if (is(T[$-1] == LLVMFile)) alias T[0 .. $-1] T2;
    else alias T T2;
    
    static if (T2.length && is(T2[0]: Namespace)) alias T2[1 .. $] T3;
    else alias T2 T3;
    
    static if (T3.length && is(T3[0]: int)) alias T3[1 .. $] T4;
    else alias T3 T4;
    
    static assert(T4.length % 2 == 0);
    
    auto myns = fastalloc!(MiniNamespace)(id);
    // at exit, stop matching lookups with internal members
    // this is for when we're parsing sub-scopes underneath us
    // but the main MiniNamespace parsing is over. 
    // this pretty much only happens in fun.d:function_open.
    scope(exit) myns.field.clean;
    
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
        todo("fs2 unsupport");
        // myns.fs2 = _t[1];
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
      if (!t[i*2+1]) fail;
      // dup because arguments may be static char arrays
      myns.add(t[i*2].dup, t[i*2+1]);
    }
    
    static if (is(T[$-1] == LLVMFile)) {
      static assert(false, "TODO: LLVMFile");
      todo("fs set");
      // myns.fs = t[$-1].currentStackDepth;
    }
    
    myns.internalMode = allInternal;
    
    sourcefiles["<internal:"~id~">"] = text;
    
    auto res = parse(text, rule);
    auto rc = fastcast!(R) (res);
    static if (mustParse) {
      if (text.mystripl().length) text.failparse("Unknown text: '"~text~"'"[]);
      if (!res)                text.failparse("Failed to parse"[]);
      if (!rc)                 text.failparse("Wrong result type: wanted "[], R.stringof, "[], got "[], res);
    } else {
      if (text.length || !rc) return null;
    }
    if (optres) opt(rc);
    return rc;
  }
}

Object gotNamedType(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id, true) && !(id in reserved)) {
    retry:
    try if (auto obj = namespace().lookup(id)) {
      if (auto type = fastcast!(IType) (obj)) {
        text = t2;
        return fastcast!(Object) (forcedConvert(type));
      } else {
        return null;
      }
    }
    else if (t2.eatDash(id)) goto retry;
    else if (t2.eatDot(id)) goto retry;
    catch (Exception ex) {
      text.failparse(ex);
    }
  }
  return null;
}
mixin DefaultParser!(gotNamedType, "type.named"[], "21"[]);

class LengthOverride : Namespace, ScopeLike {
  Expr len;
  this(Namespace sup, Expr ex) { this.sup = sup; len = ex; }
  override {
    Statement[] getGuards() { return sup.get!(ScopeLike).getGuards(); }
    int[] getGuardOffsets() { return sup.get!(ScopeLike).getGuardOffsets(); }
    string mangle(string name, IType type) { return sup.mangle(name, type); }
    Stuple!(IType, string)[] stackframe() { return sup.get!(ScopeLike).stackframe(); }
    string toString() { return Format("[$ = "[], len, "] <- "[], sup); }
    Object lookup(string name, bool local = false) {
      if (name == "$"[]) return fastcast!(Object)~ len;
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
void noop() { }
template ImporterImpl(alias parseme = noop) {
  Namespace[] imports, public_imports, static_imports;
  Namespace[] getImports() {
    parseme();
    return imports ~ public_imports ~ static_imports;
  }
  bool[] importsUsed; // print warnings on unused imports (but NOT public ones!)
  Namespace[]* getImportsPtr(ImportType type) {
    switch (type) {
      case ImportType.Regular: return &imports;
      case ImportType.Public: return &public_imports;
      case ImportType.Static: return &static_imports;
    }
  }
  void checkImportsUsage() { parseme(); ast.namespace.check_imports_usage(name, imports, importsUsed); }
  Object lookupInImports(string name, bool local) {
    Object res;
    Namespace source;
    const debug_lookup = false;
    void addres(Object obj, Namespace src) {
      static if (debug_lookup) logln("mew: "[], name, " => "[], obj, " - "[], obj.classinfo.name);
      if (!res) { res = obj; source = src; return; }
      auto ex = fastcast!(Extensible) (res), ex2 = fastcast!(Extensible)(obj);
      if (ex && !ex2 || !ex && ex2) {
        throw new Exception(Format("While looking up "[], name, ": ambiguity between "[],
          res, " and "[], obj, ": one is overloadable and the other isn't"[]));
      }
      if (!ex) {
        if (res is obj) return;
        auto t1 = fastcast!(IType) (res);
        auto t2 = fastcast!(IType) (obj);
        if (t1 && t2 && t1 == t2) return;
        throw new Exception(Format(
          "Name ambiguous: '", name, "' can refer to both ", source, ".", name, " and ", src, ".", name
        ));
        // fail;
      }
      res = fastcast!(Object) (ex.extend(ex2));
    }
    void finalize() {
      auto xt = fastcast!(Extensible) (res);
      if (!xt) return;
      if (auto simp = xt.simplify()) res = fastcast!(Object) (simp);
    }
    
    foreach (ns; public_imports) {
      static if (debug_lookup) logln("1: "[], name, " in "[], ns, "?"[]);
      if (auto res = ns.lookup(name, true)) {
        addres(res, ns);
      }
    }
    
    foreach (ns; static_imports) if (auto imod = fastcast!(IModule) (ns)) {
      static if (debug_lookup) logln("2: "[], name, " in "[], ns, "?"[]);
      if (auto lname = parseBase.startsWith(parseBase.startsWith(name, imod.getIdentifier()), ".")) {
        if (auto res = ns.lookup(lname)) return res;
      }
    }
    
    if (local) {
      finalize;
      static if (debug_lookup) logln("local: "[], res);
      return res;
    }
    
    foreach (i, ns; imports) {
      static if (debug_lookup) logln("3: "[], name, " in "[], ns, "?"[]);
      if (auto res = ns.lookup(name, true)) {
        *getPtrResizing(importsUsed, i) = true;
        addres(res, ns);
      }
    }
    
    if (sysmod && sysmod !is this && name != "std.c.setjmp"[])
      if (auto res = sysmod.lookup(name, true))
        addres(res, sysmod);
    
    finalize;
    static if (debug_lookup) logln("nonlocal: "[], res);
    return res;
  }
}

abstract class NamespaceImporter : Namespace, Importer {
}

NamespaceImporter sysmod;

// namespace that shouldn't be protected from accidental shadowing
interface ISafeSpaceTag { }

extern(C) bool C_showsAnySignOfHaving(Expr ex, string thing);
bool showsAnySignOfHaving(Expr ex, string thing) {
  return C_showsAnySignOfHaving(ex, thing);
}

int framelength() {
  return framelength2(namespace().get!(ScopeLike));
}

string frametype() {
  return frametype2(namespace().get!(ScopeLike));
}

string frametypePlus(IType it) {
  string type;
  foreach (entry; namespace().get!(ScopeLike).stackframe()) {
    if (type) type ~= ", ";
    type ~= typeToLLVM(entry._0);
  }
  if (type) type ~= ", ";
  type ~= typeToLLVM(it);
  return qformat("{", type, "}");
}
