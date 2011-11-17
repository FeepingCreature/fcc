module ast.macros;

import parseBase, ast.base, ast.literal_string, ast.tuples, ast.fun, ast.funcall,
       ast.namespace, ast.tuple_access, ast.variable, ast.vardecl, ast.scopes,
       ast.aggregate, ast.assign, ast.ifstmt;

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
  if (src.accept("\"")) {
    auto mew = src.slice("\"");
    return new Escape(new Token(mew)); // haaaaax
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
  string getIdentifier() { return identifier; }
  this(Entity e) { root = e; identifier = Format("__tenth_macro_", macrocount++); }
}

Context rootctx;
void initTenth() {
  if (rootctx) return;
  rootctx = new Context;
  rootctx.add("nil", NilEnt);
  rootctx.add("t", NonNilEnt);
  rootctx.add("last", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    return args[$-1];
  }));
  rootctx.add("def", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Too many arguments to def: 2 expected");
    mixin(chaincast("tok: First arg to def: args[0]->Token: %.name"));
    ctx.add(tok, args[1]);
    return args[1];
  }));
  rootctx.add("make-tuple-expr", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to make-tuple-expr: 1 expected");
    mixin(chaincast("list: Argument to make-tuple-expr: args[0]->List"));
    Expr[] exlist = new Expr[list.entries.length];
    foreach (i, e; list.entries) {
      mixin(chaincast("ex: List entry for make-tuple-expr: e->ItrEntity: %.itr->Expr"));
      exlist[i] = ex;
    }
    return new ItrEntity(mkTupleExpr(exlist));
  }));
  rootctx.add("make-call", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to make-call: 2 expected");
    mixin(chaincast("fun: First arg for make-call: args[0]->ItrEntity: %.itr->Function"));
    mixin(chaincast("ex: Second arg for make-call: args[1]->ItrEntity: %.itr->Expr"));
    return new ItrEntity(buildFunCall(fun, ex, "tenth-call"));
  }));
  rootctx.add("make-if", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-if': 2 expected");
    mixin(chaincast("cd: First arg for 'make-if': args[0]->ItrEntity: %.itr->Cond"));
    mixin(chaincast("st: Second arg for 'make-if': args[1]->ItrEntity: %.itr->Statement"));
    auto ifs = new IfStatement;
    ifs.wrapper = new Scope;
    ifs.test = cd;
    ifs.branch1 = new Scope;
    ifs.branch1.addStatement(st);
    return new ItrEntity(ifs);
  }));
  rootctx.add("substitute", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to 'substitute': 3 expected");
    mixin(chaincast("itr: First arg for 'substitute': args[0]->ItrEntity: %.itr"));
    mixin(chaincast("from: Second arg for 'substitute': args[1]->ItrEntity: %.itr"));
    mixin(chaincast("to: Third arg for 'substitute': args[2]->ItrEntity: %.itr"));
    void subst(ref Iterable it) {
      if (it == from) it = to;
      it.iterate(&subst);
    }
    itr = itr.dup();
    subst(itr);
    return new ItrEntity(itr);
  }));
  rootctx.add("lookup", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to lookup: 1 expected");
    mixin(chaincast("tok: Arg for lookup: args[0]->Token: %.name"));
    auto res = fastcast!(Tree) (namespace().lookup(tok));
    if (!res) tnte("No such object: ", tok);
    return new ItrEntity(res);
  }));
  rootctx.add("not", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'not': 1 expected");
    if (isNil(args[0])) return NonNilEnt;
    else return NilEnt;
  }));
  rootctx.add("or", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'or': >=1 expected");
    bool res = false;
    foreach (arg; args) res |= !isNil(arg);
    if (res) return NonNilEnt;
    else return NilEnt;
  }));
  rootctx.add("and", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'and': >=1 expected");
    bool res = true;
    foreach (arg; args) res &= !isNil(arg);
    if (res) return NonNilEnt;
    else return NilEnt;
  }));
  rootctx.add("if", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to 'if': 3 expected");
    auto cond = args[0];
    bool bcond = !isNil(cond);
    if (bcond) return args[1].eval(ctx);
    else return args[2].eval(ctx);
  }));
  rootctx.add("make-temporary", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-temporary': 1 expected");
    mixin(chaincast("ty: Arg for make-temporary: args[0]->TypeEntity: %.ty"));
    auto var = new Variable(ty, null, boffs(ty));
    var.dontInit = true;
    auto sc = namespace().get!(Scope);
    sc.add(var);
    sc.addStatement(new VarDecl(var));
    return new ItrEntity(var);
  }));
  rootctx.add("type-of", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'type-of': 1 expected");
    mixin(chaincast("ty: Arg for type-of: args[0]->ItrEntity: %.itr->Expr: %.valueType()"));
    return new TypeEntity(ty);
  }));
  rootctx.add("make-sae", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-sae': 2 expected");
    mixin(chaincast("st: First arg for make-sae: args[0]->ItrEntity: %.itr->Statement"));
    mixin(chaincast("ex: Second arg for make-sae: args[1]->ItrEntity: %.itr->Expr"));
    return new ItrEntity(mkStatementAndExpr(st, ex));
  }));
  rootctx.add("make-aggregate", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-aggregate': 1 expected");
    mixin(chaincast("list: Arg for make-aggregate: args[0]->List"));
    auto res = new AggrStatement;
    foreach (ent; list.entries) {
      mixin(chaincast("st: List entry for make-aggregate: ent->ItrEntity: %.itr->Statement"));
      res.stmts ~= st;
    }
    return new ItrEntity(res);
  }));
  rootctx.add("make-assignment", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-assignment': 2 expected");
    mixin(chaincast("dest: First arg for make-assignment: args[0]->ItrEntity: %.itr->Expr"));
    mixin(chaincast("src: Second arg for make-assignment: args[1]->ItrEntity: %.itr->Expr"));
    return new ItrEntity(mkAssignment(dest, src));
  }));
  rootctx.add("make-placeholder", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-placeholder': 1 expected");
    mixin(chaincast("type: Arg for make-placeholder: args[0]->TypeEntity: %.ty"));
    return new ItrEntity(new PlaceholderToken(type, "Tenth macro placeholder"));
  }));
  rootctx.add("make-tuple-index", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-tuple-index': 2 expected");
    mixin(chaincast("tup: First arg for make-tuple-index: args[0]->ItrEntity: %.itr->Expr"));
    mixin(chaincast("index: Second arg for make-tuple-index: args[1]->Integer: %.value"));
    return new ItrEntity(mkTupleIndexAccess(tup, index));
  }));
  rootctx.add("with-scope", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'with-scope': 1 expected");
    auto sc = new Scope;
    namespace.set(sc);
    auto thing = args[0].eval(ctx);
    mixin(chaincast("st: Result of with-scope arg0: thing->ItrEntity: %.itr -> Statement"));
    sc.addStatement(st);
    namespace.set(sc.sup);
    return new ItrEntity(sc);
  }));
  rootctx.add("insert-scope", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'insert-scope': 2 expected");
    mixin(chaincast("name: First arg for 'insert-scope': args[0]->Token: %.name"));
    mixin(chaincast("tr: Second arg for 'insert-scope': args[1]->ItrEntity: %.itr"));
    namespace().add(name, tr);
    return args[1];
  }));
  rootctx.add("remove-scope", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'remove-scope': 1 expected");
    mixin(chaincast("name: First arg for 'remove-scope': args[0]->Token: %.name"));
    namespace().field_cache.remove(name);
    namespace().rebuildField;
    return NonNilEnt;
  }));
  rootctx.add("list", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    return new List(args);
  }));
  rootctx.add("length", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'length': 1 expected");
    mixin(chaincast("len: Arg to 'length': args[0]->List: %.entries.length"));
    return new Integer(len);
  }));
  rootctx.add("tuple-length", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'tuple-length': 1 expected");
    mixin(chaincast("len: Arg to 'tuple-length': args[0]->ItrEntity: %.itr->Expr: %.valueType()->Tuple: %.types.length"));
    return new Integer(len);
  }));
  rootctx.add("tuple-exprs", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'tuple-exprs': 1 expected");
    mixin(chaincast("exprs: Arg to 'tuple-exprs': args[0]->ItrEntity: %.itr->Expr: getTupleEntries(%)"));
    auto list = new Entity[exprs.length];
    foreach (i, ex; exprs) list[i] = new ItrEntity(ex);
    return new List(list);
  }));
  rootctx.add("for", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3 && args.length != 4) tnte("Wrong number of args to 'for': 3 or 4 expected");
    auto loopct = new Context;
    loopct.sup = ctx;
    Entity[] res;
    if (args.length == 4) {
      mixin(chaincast(" from:  First arg to 'for': args[0]->Integer: %.value"));
      mixin(chaincast("   to: Second arg to 'for': args[1]->Integer: %.value"));
      mixin(chaincast("ident:  Third arg to 'for': args[2]->Token: %.name"));
      res = new Entity[to-from];
      for (int i = from; i < to; ++i) {
        loopct.add(ident, new Integer(i));
        res[i] = args[3].eval(loopct);
      }
    } else {
      mixin(chaincast("list: First arg to 'for': args[0]->List: %.entries"));
      mixin(chaincast("ident: Second arg to 'for': args[1]->Token: %.name"));
      res = new Entity[list.length];
      foreach (i, ent; list) {
        loopct.add(ident, ent);
        res[i] = args[2].eval(loopct);
      }
    }
    return new List(res);
  }));
  rootctx.add("while", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'while': 2 expected");
    Entity[] res;
    while (!isNil(args[0].eval(ctx)))
      res ~= args[1].eval(ctx);
    return new List(res);
  }));
  rootctx.add("lambda", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'lambda': 3 or 4 expected");
    return new DgCallable(stuple(ctx, args) /apply/
      delegate Entity(Context prevctx, Entity[] prevargs, Context ctx, Entity[] args) {
        mixin(chaincast("paramlist: Parameter list for 'lambda': prevargs[0]->List: %.entries"));
        if (paramlist.length != args.length)
          tnte("Invalid number of parameters to lambda ", prevargs, ": ", args);
        auto innerctx = new Context(prevctx);
        foreach (i, par; paramlist) {
          mixin(chaincast("name: Argument declaration for 'lambda': par->Token: %.name"));
          innerctx.add(name, args[i]);
        }
        return prevargs[1].eval(innerctx);
      }
    );
  }));
}

Object runTenth(Object obj, ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto mac = fastcast!(TenthMacro) (obj);
  auto findme = namespace().lookup(mac.identifier, false);
  if (findme !is mac) return null; // check if we're in scope
  auto ent = mac.root;
  initTenth;
  auto ctx = new Context(rootctx);
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
    return new ItrEntity(tup);
  }));
  ctx.add("parse-expr", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-expr: 0 expected");
    Expr ex;
    if (!rest(t2, "tree.expr", &ex)) t2.failparse("Expression expected");
    return new ItrEntity(ex);
  }));
  ctx.add("parse-stmt", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-stmt: 0 expected");
    Statement st;
    if (!rest(t2, "tree.stmt", &st)) t2.failparse("Statement expected");
    return new ItrEntity(st);
  }));
  ctx.add("parse-cond", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-cond: 0 expected");
    Cond cd;
    if (!rest(t2, "cond", &cd)) t2.failparse("Condition expected");
    return new ItrEntity(cd);
  }));
  ctx.add("parse-type", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to 'parse-type': 0 expected");
    Type ty;
    if (!rest(t2, "type", &ty))
      t2.failparse("Type expected");
    return new TypeEntity(ty);
  }));
  ctx.add("matched-text", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'matched-text': 1 expected");
    mixin(chaincast("tok: Argument to matched-text: args[0]->Token: %.name"));
    if (!t2.accept(tok)) {
      return NilEnt;
    }
    return NonNilEnt;
  }));
  ctx.add("match-text", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'match-text': 1 expected");
    mixin(chaincast("tok: Argument to 'match-text': args[0]->Token: %.name"));
    if (!t2.accept(tok)) {
      t2.failparse("Expected \"", tok, "\"");
    }
    return NonNilEnt;
  }));
  auto res = ent.eval(ctx);
  if (isNil(res)) return null;
  auto ie = fastcast!(ItrEntity) (res);
  if (!ie) tnte("Macro must evaluate to tree, not ", res);
  text = t2;
  return fastcast!(Object) (ie.itr);
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
