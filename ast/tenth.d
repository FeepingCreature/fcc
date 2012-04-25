module ast.tenth;

import ast.base, ast.types;
import tools.base: This, This_fn, rmSpace;

class TenthException : Exception {
  this(string s) { super("TenthException: "~s); }
}

// throw new TenthException
void tnte(T...)(T t) {
  throw new TenthException(Format(t));
}

class Context {
  Entity[string] defs;
  Context sup;
  this() { }
  this(Context c) { sup = c; }
  string toString() {
    if (!sup) return Format("context ", defs.keys);
    return Format("context ", defs.keys, " <- ", sup);
  }
  Entity lookup(string s) {
    if (auto p = s in defs) return *p;
    if (sup) return sup.lookup(s);
    return null;
  }
  void add(string name, Entity ent) { defs[name] = ent; }
}

abstract class Entity {
  Entity eval(Context);
}

class Token : Entity {
  string name;
  mixin This!("name");
  string toString() { return name; }
  override Entity eval(Context ctx) {
    auto res = ctx.lookup(name);
    if (!res) throw new Exception(Format("Could not evaluate '", name, "': no such entity in ", ctx));
    return res;
  }
}

class Integer : Entity {
  int value;
  mixin This!("value");
  string toString() { return Format(value); }
  override Entity eval(Context ctx) { return this; }
}

class Escape : Entity {
  Entity sub;
  mixin This!("sub");
  string toString() { return Format("'", sub); }
  override Entity eval(Context) { return sub; }
}

interface Callable {
  Entity call(Context, Entity[] args);
}

class List : Entity {
  Entity[] entries;
  mixin This!("entries = null");
  string toString() { string res; foreach (i, ent; entries) { if (i) res ~= " "; res ~= Format(ent); } return "(" ~ res ~ ")"; }
  override Entity eval(Context ctx) {
    if (!entries.length)
      tnte("Cannot evaluate empty list. ");
    
    auto first = entries[0].eval(ctx);
    auto firstc = fastcast!(Callable) (first);
    if (!firstc)
      tnte("First element of list is not callable: ", first);
    
    Entity[] args = new Entity[entries.length - 1];
    foreach (i, ent; entries[1..$]) {
      args[i] = ent.eval(ctx);
      if (!args[i]) {
        logln("fail: ", ent, " is a ", (cast(Object) ent).classinfo.name);
        fail;
      }
    }
    return firstc.call(ctx, args);
  }
}

Entity NilEnt, NonNilEnt;
static this() {
  NilEnt = fastalloc!(List)();
  NonNilEnt = fastalloc!(List)([new List]);
}

class DgCallable : Entity, Callable {
  Entity delegate(Context, Entity[]) dg;
  mixin This!("dg");
  override Entity eval(Context) { assert(false); }
  Entity call(Context ctx, Entity[] args) {
    return dg(ctx, args);
  }
}

Entity _parseTenth(ref string src) {
  if (src.accept("'")) {
    return fastalloc!(Escape)(_parseTenth(src));
  }
  if (src.accept("\"")) {
    auto mew = src.slice("\"");
    return fastalloc!(Escape)(fastalloc!(Token)(mew)); // haaaaax
  }
  if (src.accept("(")) {
    Entity[] res;
    while (true) {
      if (src.accept(")")) return fastalloc!(List)(res);
      res ~= _parseTenth(src);
    }
  }
  int val;
  if (src.gotInt(val)) {
    return fastalloc!(Integer)(val);
  }
  string id;
  if (src.gotIdentifier(id)) {
    return fastalloc!(Token)(id);
  }
  src.failparse("Unknown Tenth code");
}

Entity parseTenth(string s) {
  return _parseTenth(s);
}

class ItrEntity : Entity {
  Iterable itr;
  mixin This!("itr");
  string toString() { return Format("<", itr, ">"); }
  override Entity eval(Context ctx) {
    tnte("Tried to evaluate iterable entity: ", itr);
    assert(false);
  }
}

class TypeEntity : Entity {
  IType ty;
  mixin This!("ty");
  string toString() { return Format("<", ty, ">"); }
  override Entity eval(Context ctx) {
    tnte("Tried to evaluate type entity: ", ty);
    assert(false);
  }
}

bool isNil(Entity ent) {
  auto li = fastcast!(List) (ent);
  if (!li) return false;
  return li.entries.length == 0;
}

import tools.ctfe;
string chaincast(string mode) {
  auto target = mode.ctSlice(":").ctStrip();
  auto prefix = mode.ctSlice(":").ctStrip();
  string res;
  int i;
  string currentTemp;
  while (mode.ctStrip().length) {
    auto castto = mode.ctSlice(":").ctStrip();
    auto ex = castto.ctSlice("->");
    if (currentTemp) {
      ex = ex.ctReplace("%", currentTemp);
      i++;
      auto transformedTemp = target~"_pre_"~ctToString(i);
      res ~= "auto "~transformedTemp~" = "~ex~";\n";
      currentTemp = transformedTemp;
    } else {
      currentTemp = target~"_pre_"~ctToString(i);
      res = "auto "~currentTemp~ " = "~ex~";\n";
    }
    if (castto) {
      i++;
      auto newTemp = target~"_pre_"~ctToString(i);
      res ~= "auto "~newTemp~" = fastcast!("~castto~") ("~currentTemp~");\n";
      res ~= "if (!"~newTemp~") tnte(\""~prefix~" must be "~castto~", not \", "~currentTemp~");\n";
      currentTemp = newTemp;
    }
  }
  res ~= "auto "~target~" = "~currentTemp~";\n";
  return res;
}

int macrocount;
class TenthMacro : NoOp, Named {
  string identifier;
  Entity root;
  string key;
  string getIdentifier() { return identifier; }
  this(Entity e, string key) { root = e; this.key = key; identifier = Format("__tenth_macro_", macrocount++); }
}

Context rootctx;

extern(C) void fcc_initTenth();

Object runTenthPure(void delegate(void delegate(string, Object)) setupDg, Entity root) {
  fcc_initTenth;
  auto ctx = fastalloc!(Context)(rootctx);
  setupDg((string name, Object obj) {
    if (auto itr = fastcast!(Iterable) (obj)) {
      ctx.add(name, fastalloc!(ItrEntity)(itr));
      return;
    }
    if (auto ty = fastcast!(Type) (obj)) {
      ctx.add(name, fastalloc!(TypeEntity)(ty));
      return;
    }
    logln("No idea now to add ", name, ": ", obj);
    fail;
  });
  auto res = root.eval(ctx);
  if (auto itr = fastcast!(ItrEntity) (res))
    return fastcast!(Object) (itr.itr);
  if (auto ty = fastcast!(TypeEntity) (res))
    return fastcast!(Object) (ty.ty);
  logln("No idea how to unwrap/return ", res);
  fail;
}
