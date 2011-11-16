module ast.macros;

import parseBase, ast.base, ast.literal_string, ast.tuples, ast.fun, ast.funcall,
       ast.namespace, ast.tuple_access, ast.variable, ast.vardecl, ast.scopes,
       ast.aggregate, ast.assign;

import tools.base: This;

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
      return this;
    
    auto first = entries[0].eval(ctx);
    auto firstc = fastcast!(Callable) (first);
    if (!firstc)
      tnte("First element of list is not callable: ", first);
    
    Entity[] args = new Entity[entries.length - 1];
    foreach (i, ent; entries[1..$]) {
      args[i] = ent.eval(ctx);
      if (!args[i]) {
        logln("fail: ", ent, " is a ", (cast(Object) ent).classinfo.name);
        asm { int 3; }
      }
    }
    return firstc.call(ctx, args);
  }
}

Entity NilEnt, NonNilEnt;
static this() {
  NilEnt = new List();
  NonNilEnt = new List([new List]);
}

class DgCallable : Entity, Callable {
  Entity delegate(Context, Entity[]) dg;
  mixin This!("dg");
  override Entity eval(Context) { assert(false); }
  Entity call(Context ctx, Entity[] args) {
    return dg(ctx, args);
  }
}

Entity parseTenth(ref string src) {
  if (src.accept("'")) {
    return new Escape(parseTenth(src));
  }
  if (src.accept("(")) {
    Entity[] res;
    while (true) {
      if (src.accept(")")) return new List(res);
      res ~= parseTenth(src);
    }
  }
  int val;
  if (src.gotInt(val)) {
    return new Integer(val);
  }
  string id;
  if (src.gotIdentifier(id)) {
    return new Token(id);
  }
  src.failparse("Unknown Tenth code");
}

class TreeEntity : Entity {
  Tree tr;
  mixin This!("tr");
  string toString() { return Format("<", tr, ">"); }
  override Entity eval(Context ctx) {
    tnte("Tried to evaluate tree entity: ", tr);
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
  string getIdentifier() { return identifier; }
  this(Entity e) { root = e; identifier = Format("__tenth_macro_", macrocount++); }
}

Object runTenth(Object obj, ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto mac = fastcast!(TenthMacro) (obj);
  auto findme = namespace().lookup(mac.identifier, false);
  if (findme !is mac) return null; // check if we're in scope
  auto ent = mac.root;
  auto ctx = new Context;
  ctx.add("last", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    return args[$-1];
  }));
  ctx.add("def", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Too many arguments to def: 2 expected");
    mixin(chaincast("tok: First arg to def: args[0]->Token: %.name"));
    ctx.add(tok, args[1]);
    return args[1];
  }));
  ctx.add("parse-ident", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-ident: 0 expected");
    string ident;
    if (!t2.gotIdentifier(ident))
      t2.failparse("Identifier expected");
    return new Token(ident);
  }));
  ctx.add("parse-tuple", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-tuple: 0 expected");
    Expr tup;
    if (!rest(t2, "tree.expr _tree.expr.arith", &tup)
     || !fastcast!(Tuple) (tup.valueType()))
      t2.failparse("Tuple expected");
    return new TreeEntity(tup);
  }));
  ctx.add("matched-ident", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to matched-ident: 1 expected");
    mixin(chaincast("tok: Argument to matched-ident: args[0]->Token: %.name"));
    if (!t2.accept(tok)) {
      return NilEnt;
    }
    return NonNilEnt;
  }));
  ctx.add("make-tuple-expr", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to make-tuple-expr: 1 expected");
    mixin(chaincast("list: Argument to make-tuple-expr: args[0]->List"));
    Expr[] exlist = new Expr[list.entries.length];
    foreach (i, e; list.entries) {
      auto te = fastcast!(TreeEntity) (e);
      if (!te) tnte("List for make-tuple-expr must contain Exprs, not ", e);
      auto ex = fastcast!(Expr) (te.tr);
      if (!ex) tnte("List for make-tuple-expr must contain Exprs, not ", te.tr);
      exlist[i] = ex;
    }
    return new TreeEntity(mkTupleExpr(exlist));
  }));
  ctx.add("make-call", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to make-call: 2 expected");
    mixin(chaincast("fun: First arg for make-call: args[0]->TreeEntity: %.tr->Function"));
    mixin(chaincast("ex: Second arg for make-call: args[1]->TreeEntity: %.tr->Expr"));
    return cast(Entity) (new TreeEntity(buildFunCall(fun, ex, "tenth-call")));
  }));
  ctx.add("lookup", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to lookup: 1 expected");
    mixin(chaincast("tok: Arg for lookup: args[0]->Token: %.name"));
    auto res = fastcast!(Tree) (namespace().lookup(tok));
    if (!res) tnte("No such object: ", tok);
    return new TreeEntity(res);
  }));
  ctx.add("not", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'not': 1 expected");
    if (isNil(args[0])) return NonNilEnt;
    else return NilEnt;
  }));
  ctx.add("if", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to 'if': 3 expected");
    auto cond = args[0];
    bool bcond = !isNil(cond);
    if (bcond) return args[1].eval(ctx);
    else return args[2].eval(ctx);
  }));
  ctx.add("make-temporary", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-temporary': 1 expected");
    mixin(chaincast("ty: Arg for make-temporary: args[0]->TypeEntity: %.ty"));
    auto var = new Variable(ty, null, boffs(ty));
    var.dontInit = true;
    auto sc = namespace().get!(Scope);
    sc.add(var);
    sc.addStatement(new VarDecl(var));
    return new TreeEntity(var);
  }));
  ctx.add("type-of", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'type-of': 1 expected");
    mixin(chaincast("ty: Arg for type-of: args[0]->TreeEntity: %.tr->Expr: %.valueType()"));
    return new TypeEntity(ty);
  }));
  ctx.add("make-sae", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-sae': 2 expected");
    mixin(chaincast("st: First arg for make-sae: args[0]->TreeEntity: %.tr->Statement"));
    mixin(chaincast("ex: Second arg for make-sae: args[1]->TreeEntity: %.tr->Expr"));
    return new TreeEntity(mkStatementAndExpr(st, ex));
  }));
  ctx.add("make-aggregate", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-aggregate': 1 expected");
    mixin(chaincast("list: Arg for make-aggregate: args[0]->List"));
    auto res = new AggrStatement;
    foreach (ent; list.entries) {
      mixin(chaincast("st: List entry for make-aggregate: ent->TreeEntity: %.tr->Statement"));
      res.stmts ~= st;
    }
    return new TreeEntity(res);
  }));
  ctx.add("make-assignment", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-assignment': 2 expected");
    mixin(chaincast("dest: First arg for make-assignment: args[0]->TreeEntity: %.tr->Expr"));
    mixin(chaincast("src: Second arg for make-assignment: args[1]->TreeEntity: %.tr->Expr"));
    return new TreeEntity(mkAssignment(dest, src));
  }));
  ctx.add("make-tuple-index", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-tuple-index': 2 expected");
    mixin(chaincast("tup: First arg for make-tuple-index: args[0]->TreeEntity: %.tr->Expr"));
    mixin(chaincast("index: Second arg for make-tuple-index: args[1]->Integer: %.value"));
    return new TreeEntity(mkTupleIndexAccess(tup, index));
  }));
  ctx.add("list", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    return new List(args);
  }));
  ctx.add("tuple-length", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'tuple-length': 1 expected");
    mixin(chaincast("len: Arg to 'tuple-length': args[0]->TreeEntity: %.tr->Expr: %.valueType()->Tuple: %.types.length"));
    return new Integer(len);
  }));
  ctx.add("for", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to 'for': 3 expected");
    mixin(chaincast("range: First arg to 'for': args[0]->List"));
    if (range.entries.length != 2) tnte("Wrong number of range parts to 'for': 2 expected");
    mixin(chaincast("from: Lower end of range to 'for': range.entries[0]->Integer: %.value"));
    mixin(chaincast("  to: Upper end of range to 'for': range.entries[1]->Integer: %.value"));
    mixin(chaincast("ident: Second arg to 'for': args[1]->Token: %.name"));
    auto loopct = new Context;
    loopct.sup = ctx;
    Entity[] res = new Entity[to-from];
    for (int i = from; i < to; ++i) {
      loopct.add(ident, new Integer(i));
      res[i] = args[2].eval(loopct);
    }
    return new List(res);
  }));
  ctx.add("map-tuple", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to map-tuple: 3 expected");
    mixin(chaincast("tup: First arg for map-tuple: args[0]->TreeEntity: %.tr->Expr"));
    mixin(chaincast("ident: Second arg for map-tuple: args[1]->Token: %.name"));
    auto entries = getTupleEntries(tup);
    Entity[] res;
    auto loopct = new Context;
    loopct.sup = ctx;
    foreach (ex; entries) {
      loopct.add(ident, new TreeEntity(ex));
      res ~= args[2].eval(loopct);
    }
    return new List(res);
  }));
  auto res = ent.eval(ctx);
  if (isNil(res)) return null;
  auto tr = fastcast!(TreeEntity) (res);
  if (!tr) tnte("Macro must evaluate to tree, not ", res);
  text = t2;
  return fastcast!(Object) (tr.tr);
}

Object gotMacroStmt(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("(")) text.failparse("Opening paren expected. ");
  StringExpr rulename, ruleid;
  if (!rest(text, "tree.expr _tree.expr.arith", &rulename))
    text.failparse("Rule name expected");
  if (!text.accept(","))
    text.failparse("Comma expected");
  if (!rest(text, "tree.expr _tree.expr.arith", &ruleid))
    text.failparse("Rule ID expected");
  if (!text.accept(")"))
    text.failparse("Closing paren expected. ");
  StringExpr src;
  if (!rest(text, "tree.expr _tree.expr.arith", &src))
    text.failparse("Expected source string");
  if (!text.accept(";"))
    text.failparse("Closing semicolon expected");
  Object obj;
  {
    auto s2 = src.str;
    auto ent = parseTenth(s2);
    auto mac = new TenthMacro(ent);
    obj = mac;
  }
  auto dpi = new DefaultParserImpl!(runTenth, null, true, null)(obj);
  dpi.id = rulename.str;
  parsecon.addParser(dpi, ruleid.str);
  return obj;
}
mixin DefaultParser!(gotMacroStmt, "tree.toplevel.macro", null, "macro");
