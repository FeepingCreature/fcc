module ast.macros;

import parseBase, ast.base, ast.literal_string, ast.tuples, ast.fun, ast.funcall,
       ast.namespace, ast.tuple_access;

import tools.base: This;

class TenthException : Exception {
  this(string s) { super("TenthException: "~s); }
}

class AbortException : Exception {
  this() { super("mew"); }
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
  override Entity eval(Context ctx) {
    return ctx.lookup(name);
  }
}

class Escape : Entity {
  Entity sub;
  mixin This!("sub");
  override Entity eval(Context) { return sub; }
}

interface Callable {
  Entity call(Context, Entity[] args);
}

class List : Entity {
  Entity[] entries;
  mixin This!("entries");
  override Entity eval(Context ctx) {
    if (!entries.length)
      tnte("Cannot evaluate empty list");
    auto first = entries[0].eval(ctx);
    auto firstc = fastcast!(Callable) (first);
    if (!firstc)
      tnte("First element of list is not callable: ", first);
    return firstc.call(ctx, entries[1..$]);
  }
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
  string id;
  if (src.gotIdentifier(id)) {
    return new Token(id);
  }
  src.failparse("Unknown Tenth code");
}

class TreeEntity : Entity {
  Tree tr;
  mixin This!("tr");
  override Entity eval(Context ctx) {
    tnte("Tried to evaluate tree entity: ", tr);
    assert(false);
  }
}

Object runTenth(Object obj, ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto ent = fastcast!(Entity) (obj);
  auto ctx = new Context;
  ctx.add("last", new DgCallable((Context ctx, Entity[] args) {
    foreach (arg; args[0..$-1])
      arg.eval(ctx);
    return args[$-1].eval(ctx);
  }));
  ctx.add("def", new DgCallable((Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Too many arguments to def: 2 expected");
    auto tok = fastcast!(Token) (args[0].eval(ctx));
    if (!tok) tnte("First arg to def must be token! ");
    auto res = args[1].eval(ctx);
    ctx.add(tok.name, res);
    return res;
  }));
  ctx.add("parse-ident", new DgCallable((Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-ident: 0 expected");
    string ident;
    if (!t2.gotIdentifier(ident))
      t2.failparse("Identifier expected");
    return fastcast!(Entity) (new Token(ident));
  }));
  ctx.add("parse-tuple", new DgCallable((Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-tuple: 0 expected");
    Expr tup;
    if (!rest(t2, "tree.expr _tree.expr.arith", &tup)
     || !fastcast!(Tuple) (tup.valueType()))
      t2.failparse("Tuple expected");
    return fastcast!(Entity) (new TreeEntity(tup));
  }));
  ctx.add("match-ident", new DgCallable((Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to match-ident: 1 expected");
    auto first = args[0].eval(ctx);
    auto tok = fastcast!(Token) (first);
    if (!tok) tnte("Argument to match-ident must be token, not ", first);
    if (!t2.accept(tok.name)) {
      throw new AbortException;
    }
    return fastcast!(Entity) (new List([]));
  }));
  ctx.add("make-tuple-expr", new DgCallable((Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to make-tuple-expr: 1 expected");
    auto ent = args[0].eval(ctx);
    auto list = fastcast!(List) (ent);
    if (!list) tnte("Argument to make-tuple-expr must evaluate to a list, not ", ent);
    Expr[] exlist = new Expr[list.entries.length];
    foreach (i, e; list.entries) {
      auto te = fastcast!(TreeEntity) (e);
      if (!te) tnte("List for make-tuple-expr must contain Exprs, not ", e);
      auto ex = fastcast!(Expr) (te.tr);
      if (!ex) tnte("List for make-tuple-expr must contain Exprs, not ", te.tr);
      exlist[i] = ex;
    }
    return fastcast!(Entity) (new TreeEntity(mkTupleExpr(exlist)));
  }));
  ctx.add("make-call", new DgCallable((Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to make-call: 2 expected");
    auto first = args[0].eval(ctx);
    auto te = fastcast!(TreeEntity) (first);
    if (!te) tnte("First arg for make-call must be Function, not ", first);
    auto fun = fastcast!(Function) (te.tr);
    if (!fun) tnte("First arg for make-call must be Function, not ", te.tr);
    auto second = args[1].eval(ctx);
    auto te2 = fastcast!(TreeEntity) (second);
    if (!te2) tnte("Second arg for make-call must be Expr, not ", second);
    auto ex = fastcast!(Expr) (te2.tr);
    if (!ex) tnte("Second arg for make-call must be Expr, not ", te2.tr);
    return cast(Entity) (new TreeEntity(buildFunCall(fun, ex, "tenth-call")));
  }));
  ctx.add("lookup", new DgCallable((Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to lookup: 1 expected");
    auto arg = args[0].eval(ctx);
    auto tok = fastcast!(Token) (arg);
    if (!tok) tnte("Arg for lookup must be token, not ", arg);
    auto res = fastcast!(Tree) (namespace().lookup(tok.name));
    if (!res) tnte("No such object: ", tok.name);
    return fastcast!(Entity) (new TreeEntity(res));
  }));
  ctx.add("map-tuple", new DgCallable((Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to map-tuple: 3 expected");
    auto first = args[0].eval(ctx);
    auto tr = fastcast!(TreeEntity) (first);
    if (!tr) tnte("First arg for map-tuple must be Expr, not ", first);
    auto tup = fastcast!(Expr) (tr.tr);
    if (!tup) tnte("First arg for map-tuple must be Expr, not ", tr.tr);
    auto entries = getTupleEntries(tup);
    auto second = args[1].eval(ctx);
    auto ident = fastcast!(Token) (second);
    if (!ident) tnte("Second arg for map-tuple must be token, not ", second);
    Entity[] res;
    auto loopct = new Context;
    loopct.sup = ctx;
    foreach (ex; entries) {
      loopct.add(ident.name, new TreeEntity(ex));
      res ~= args[2].eval(loopct);
    }
    return fastcast!(Entity) (new List(res));
  }));
  try {
    auto res = ent.eval(ctx);
    auto tr = fastcast!(TreeEntity) (res);
    if (!tr) tnte("Macro must evaluate to tree, not ", res);
    text = t2;
    return fastcast!(Object) (tr.tr);
  } catch (AbortException) {
    return null;
  }
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
    obj = parseTenth(s2);
  }
  auto dpi = new DefaultParserImpl!(runTenth, null, true, null)(obj);
  dpi.id = rulename.str;
  parsecon.addParser(dpi, ruleid.str);
  return Single!(NoOp);
}
mixin DefaultParser!(gotMacroStmt, "tree.toplevel.macro", null, "macro");
