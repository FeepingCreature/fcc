module ast.parse;

import
  ast.base, ast.namespace, ast.fun, ast.structure, ast.assign,
  ast.modules, ast.scopes, ast.aggregate, ast.ifstmt, ast.returns,
  ast.math, ast.variable, ast.literals, ast.cond, ast.loops,
  ast.pointer;

import quicksort, tools.threads;
import tools.base: min, swap, apply, New;

bool verboseParser = false;

struct ParseCb {
  Object delegate(ref string text, bool delegate(string)) dg;
  bool delegate(string) cur; string curstr;
  Object opCall(T...)(ref string text, T t) {
    static if (!T.length) {
      try return this.dg(text, cur);
      catch (Exception ex) throw new Exception(Format("Continuing after '"~curstr~"': ", ex));
    } else static if (T.length == 1) {
      static if (is(T[0]: string))
        return this.dg(text, matchrule = t[0]);
      else static if (is(typeof(*t[0])))
        return this.opCall(text, cast(string) null, t[0]);
      else
        return this.dg(text, t[0]);
    } else {
      Object pre;
      string pattern = t[0];
      if (pattern) {
        try pre = this.opCall(text, matchrule = pattern);
        catch (Exception ex) throw new Exception(Format("Matching rule '"~pattern~"' off '"~text.next_text(16)~"': ", ex));
      } else {
        pre = this.opCall(text);
      }
      static if (is(typeof(*t[1]))) {
        *t[1] = cast(typeof(*t[1])) pre;
        /*if (pre && !*t[1])
          logln("WARN: res ", pre, " isn't a ", typeof(*t[1]).stringof, "!");*/
        return cast(Object) *t[1];
      } else assert(false, Format("Pointer to object expected: ", t));
    }
  }
}

interface Parser {
  string getId();
  Object match(ref string text, ParseCb cont, ParseCb restart);
}

template DefaultParser(alias Fn, string Id, string Prec = null) {
  class DefaultParser : Parser {
    static this() {
      static if (Prec) parsecon.addParser(new DefaultParser, Prec);
      else parsecon.addParser(new DefaultParser);
    }
    override string getId() { return Id; }
    override Object match(ref string text, ParseCb cont, ParseCb rest) {
      return Fn(text, cont, rest);
    }
  }
}

import tools.log;
struct SplitIter(T) {
  T data, sep;
  T front, frontIncl, all;
  T pop() {
    for (int i = 0; i <= cast(int) data.length - cast(int) sep.length; ++i) {
      if (data[i .. i + sep.length] == sep) {
        auto res = data[0 .. i];
        data = data[i + sep.length .. $];
        front = all[0 .. $ - data.length - sep.length - res.length];
        frontIncl = all[0 .. front.length + res.length];
        return res;
      }
    }
    auto res = data;
    data = null;
    front = null;
    frontIncl = all;
    return res;
  }
}

SplitIter!(T) splitIter(T)(T d, T s) {
  SplitIter!(T) res;
  res.data = d; res.sep = s;
  res.all = res.data;
  return res;
}

class ParseContext {
  Parser[] parsers;
  string[string] prec; // precedence mapping
  void addPrecedence(string id, string val) { synchronized(this) { prec[id] = val; } }
  string lookupPrecedence(string id) {
    synchronized(this)
      if (auto p = id in prec) return *p;
    return null;
  }
  import tools.compat: split, join;
  string dumpInfo() {
    resort;
    string res;
    int maxlen;
    foreach (parser; parsers) {
      auto id = parser.getId();
      if (id.length > maxlen) maxlen = id.length;
    }
    auto reserved = maxlen + 2;
    string[] prevId;
    foreach (parser; parsers) {
      auto id = parser.getId();
      auto n = id.dup.split(".");
      foreach (i, str; n[0 .. min(n.length, prevId.length)]) {
        if (str == prevId[i]) foreach (ref ch; str) ch = ' ';
      }
      prevId = id.split(".");
      res ~= n.join(".");
      for (int i = 0; i < reserved - id.length; ++i)
        res ~= " ";
      if (auto p = id in prec) {
        res ~= ":" ~ *p;;
      }
      res ~= "\n";
    }
    return res;
  }
  bool idSmaller(Parser pa, Parser pb) {
    auto a = splitIter(pa.getId(), "."), b = splitIter(pb.getId(), ".");
    string ap, bp;
    while (true) {
      ap = a.pop(); bp = b.pop();
      if (!ap && !bp) return false; // equal
      if (ap && !bp) return true; // longer before shorter
      if (bp && !ap) return false;
      if (ap == bp) continue; // no information here
      auto aprec = lookupPrecedence(a.frontIncl), bprec = lookupPrecedence(b.frontIncl);
      if (!aprec && bprec)
        throw new Exception("Patterns "~a.frontIncl~" vs. "~b.frontIncl~": first is missing precedence info! ");
      if (!bprec && aprec)
        throw new Exception("Patterns "~a.frontIncl~" vs. "~b.frontIncl~": second is missing precedence info! ");
      if (!aprec && !bprec) return ap < bp; // lol
      if (aprec == bprec) throw new Exception("Error: patterns '"~a.frontIncl~"' and '"~b.frontIncl~"' have the same precedence! ");
      for (int i = 0; i < min(aprec.length, bprec.length); ++i) {
        // precedence needs to be _inverted_, ie. lower-precedence rules must come first
        // this is because "higher-precedence" means it binds tighter.
        // if (aprec[i] > bprec[i]) return true;
        // if (aprec[i] < bprec[i]) return false;
        if (aprec[i] < bprec[i]) return true;
        if (aprec[i] > bprec[i]) return false;
      }
      bool flip;
      // this gets a bit hairy
      // 50 before 5, but 51 after 5.
      if (aprec.length < bprec.length) { swap(aprec, bprec); flip = true; }
      for (int i = bprec.length; i < aprec.length; ++i) {
        if (aprec[i] != '0') return flip;
      }
      return !flip;
    }
  }
  void addParser(Parser p) {
    parsers ~= p;
    listModified = true;
  }
  void addParser(Parser p, string pred) {
    addParser(p);
    addPrecedence(p.getId(), pred);
  }
  bool listModified;
  void resort() {
    if (listModified) { // NOT in addParser - precedence info might not be registered yet!
      parsers.qsort(&idSmaller);
      listModified = false;
    }
  }
  Object parse(ref string text, bool delegate(string) cond, int offs = 0) {
    resort;
    bool matched;
    foreach (i, parser; parsers[offs .. $]) {
      if (cond(parser.getId())) {
        if (verboseParser) logln("TRY PARSER [", parser.getId(), "] for '", text.next_text(16), "'");
        matched = true;
        ParseCb cont, rest;
        cont.dg = (ref string text, bool delegate(string) cond) {
          return this.parse(text, cond, offs + i + 1);
        };
        cont.cur = cond;
        cont.curstr = parser.getId();
        
        rest.dg = (ref string text, bool delegate(string) cond) {
          return this.parse(text, cond);
        };
        rest.cur = cond;
        rest.curstr = parser.getId();
        
        if (auto res = parser.match(text, cont, rest)) {
          if (verboseParser) logln("    PARSER [", parser.getId(), "] succeeded with ", res, ", left '", text.next_text(16), "'");
          return res;
        }
        if (verboseParser) logln("    PARSER [", parser.getId(), "] failed");
      }
    }
    if (!matched) throw new Exception("Found no patterns to match condition! ");
    return null;
  }
  Object parse(ref string text, string cond) {
    try return parse(text, matchrule=cond);
    catch (Exception ex) throw new Exception(Format("Matching rule '"~cond~"': ", ex));
  }
}

bool delegate(string) matchrule(string rules) {
  bool delegate(string) res;
  while (rules.length) {
    auto rule = rules.slice(" ");
    res = stuple(rule, res) /apply/ (string rule, bool delegate(string) op1, string text) {
      if (op1 && !op1(text)) return false;
      
      bool smaller, greater, equal;
      if (auto rest = rule.startsWith("<")) { smaller = true; rule = rest; }
      if (auto rest = rule.startsWith(">")) { greater = true; rule = rest; }
      if (auto rest = rule.startsWith("=")) { equal = true; rule = rest; }
      
      if (!smaller && !greater && !equal)
        smaller = equal = true; // default
      
      // logln(smaller?"<":"", greater?">":"", equal?"=":"", " ", text, " against ", rule);
      if (smaller && text.startsWith(rule~".")) // all "below" in the tree
        return true;
      if (equal && text == rule)
        return true;
      if (greater && !text.startsWith(rule)) // arguable
        return true;
      return false;
    };
  }
  return res;
}

TLS!(Namespace) namespace;
ParseContext parsecon;
static this() { New(namespace, { return cast(Namespace) null; }); New(parsecon); }

bool test(T)(T t) { if (t) return true; else return false; }

Object gotModule(ref string text, ParseCb cont, ParseCb restart) {
  auto t2 = text;
  Function fn;
  Structure st;
  Tree tr;
  Module mod;
  auto backup = namespace.ptr();
  scope(exit) namespace.set(backup);
  if (t2.accept("module ") && (New(mod), namespace.set(mod), true) &&
      t2.gotIdentifier(mod.name, true) && t2.accept(";") &&
      t2.many(
        !!restart(t2, "tree.toplevel", &tr),
        { mod.entries ~= tr; }
      ) &&
      (text = t2, true)
    ) return mod;
  else return null;
}
mixin DefaultParser!(gotModule, "tree.module");

Object gotToplevel(ref string text, ParseCb cont, ParseCb rest) {
  if (auto res = rest(text, "tree.fundef")) return res;
  if (auto res = rest(text, "tree.typedef")) return res;
  if (auto res = rest(text, "tree.import")) return res;
  return null;
}
mixin DefaultParser!(gotToplevel, "tree.toplevel");

Object gotFunDef(ref string text, ParseCb cont, ParseCb rest) {
  Type ptype;
  auto t2 = text;
  Function fun;
  New(fun);
  New(fun.type);
  string parname;
  error = null;
  auto mod = cast(Module) namespace();
  assert(mod);
  if (test(fun.type.ret = cast(Type) rest(t2, "type")) &&
      t2.gotIdentifier(fun.name) &&
      t2.accept("(") &&
      // TODO: function parameters belong on the stackframe
      t2.bjoin(
        test(ptype = cast(Type) rest(t2, "type")) && (t2.gotIdentifier(parname) || ((parname = null), true)),
        t2.accept(","),
        { fun.type.params ~= stuple(ptype, parname); }
      ) &&
      t2.accept(")")
    )
  {
    fun.fixup;
    auto backup = namespace();
    scope(exit) namespace.set(backup); 
    namespace.set(fun);
    mod.addFun(fun);
    text = t2;
    if (rest(text, "tree.scope", &fun._scope)) return fun;
    else throw new Exception("Couldn't parse function scope at '"~text.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotFunDef, "tree.fundef");

Object gotScope(ref string text, ParseCb cont, ParseCb rest) {
  auto sc = new Scope;
  sc.sup = namespace();
  sc.fun = namespace().get!(Function);
  namespace.set(sc);
  scope(exit) namespace.set(sc.sup);
  auto t2 = text;
  if (rest(t2, "tree.stmt", &sc._body)) { text = t2; return sc; }
  throw new Exception("Couldn't match scope off "~text.next_text());
}
mixin DefaultParser!(gotScope, "tree.scope");

Object gotImport(ref string text, ParseCb cont, ParseCb rest) {
  string m;
  // import a, b, c;
  if (!text.accept("import ")) return null;
  auto mod = namespace().get!(Module);
  if (!(
    text.bjoin(text.gotIdentifier(m, true), text.accept(","),
    { mod.imports ~= lookupMod(m); },
    true) &&
    text.accept(";")
  )) throw new Exception("Unexpected text while parsing import statement: "~text.next_text());
  return Single!(NoOp);
}
mixin DefaultParser!(gotImport, "tree.import");

Object gotStructDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("struct ")) return null;
  string name;
  Structure.Member[] ms;
  Structure.Member sm;
  if (t2.gotIdentifier(name) && t2.accept("{") &&
      t2.many(
        test(sm.type = cast(Type) rest(t2, "type")) &&
        t2.bjoin(
          t2.gotIdentifier(sm.name),
          t2.accept(",")
          ,{ ms ~= sm; }
        ) &&
        t2.accept(";")
      ) &&
      t2.accept("}")
    )
  {
    text = t2;
    auto st = new Structure(name, ms);
    namespace().addStruct(st);
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotStructDef, "tree.typedef.struct");

Object gotBasicType(ref string text, ParseCb cont, ParseCb rest) {
  if (text.accept("void")) return Single!(Void);
  if (text.accept("size_t")) return Single!(SizeT);
  if (text.accept("int")) return Single!(SysInt);
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    if (auto st = namespace().lookupStruct(id)) {
      text = t2;
      return st;
    }
  }
  return null;
}
mixin DefaultParser!(gotBasicType, "type.basic", "5");

Object gotExtType(ref string text, ParseCb cont, ParseCb rest) {
  auto type = cast(Type) cont(text);
  if (!type) return null;
  restart:
  foreach (dg; typeModlist) {
    if (auto nt = dg(text, type)) {
      type = nt;
      goto restart;
    }
  }
  return type;
}
mixin DefaultParser!(gotExtType, "type.ext", "1");

Object gotAggregateStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  AggrStatement as;
  Statement st;
  if (t2.accept("{") && (New(as), true) &&
      t2.many(!!rest(t2, "tree.stmt", &st), { as.stmts ~= st; }) &&
      t2.mustAccept("}", Format("Encountered unknown statement at ", t2.next_text()))
    ) { text = t2; return as; }
  else return null;
}
mixin DefaultParser!(gotAggregateStmt, "tree.stmt.aggregate");

Object gotIfStmt(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text, t3;
  IfStatement ifs;
  if (t2.accept("if ") && (New(ifs), true) &&
      rest(t2, "tree.cond", &ifs.test) && rest(t2, "tree.scope", &ifs.branch1) && (
        ((t3 = t2, true) && t3.accept("else") && rest(t3, "tree.scope", &ifs.branch2) && (t2 = t3, true))
        || true
      )
    ) { text = t2; return ifs; }
  else return null;
}
mixin DefaultParser!(gotIfStmt, "tree.stmt.if");

Object gotRetStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("return ")) {
    auto rs = new ReturnStmt;
    rs.ns = namespace();
    if (rest(t2, "tree.expr", &rs.value)) {
      text = t2;
      return rs;
    } else throw new Exception("Error parsing return expression at "~t2.next_text());
  } else return null;
}
mixin DefaultParser!(gotRetStmt, "tree.semicol_stmt.return");

import tools.compat: rfind;
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
mixin DefaultParser!(gotNamed, "tree.expr.named", "4");

Object gotLiteralExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (text.gotStringExpr(ex) || text.gotIntExpr(ex)) return cast(Object) ex;
  else return null;
}
mixin DefaultParser!(gotLiteralExpr, "tree.expr.literal", "5");

Object gotBraceExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (text.accept("(") &&
      rest(text, "tree.expr", &ex)
    ) {
    text.mustAccept(")", Format("Missing closing brace at ", text.next_text()));
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotBraceExpr, "tree.expr.braces", "6");

Object gotCallExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text, sup = cont(t2);
  if (auto fun = cast(Function) sup) {
    auto fc = new FunCall;
    fc.fun = fun;
    Expr ex;
    if (t2.accept("(") &&
        t2.bjoin(!!rest(t2, "tree.expr", &ex), t2.accept(","), { fc.params ~= ex; }, false) &&
        t2.accept(")"))
    {
      text = t2;
      return fc;
    }
    else throw new Exception("While expecting function call: "~t2.next_text());
  } else return null;
}
mixin DefaultParser!(gotCallExpr, "tree.expr.funcall", "2");

Object gotVarDecl(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text, var = new Variable;
  if (rest(t2, "type", &var.type) && t2.gotIdentifier(var.name)) {
    if (t2.accept("=")) {
      if (!rest(t2, "tree.expr", &var.initval))
        throw new Exception(Format("Couldn't read expression at ", t2.next_text()));
    }
    t2.mustAccept(";", Format("Missed trailing semicolon at ", t2.next_text()));
    var.baseOffset = -(cast(Scope) namespace()).framesize() - var.type.size;
    auto vd = new VarDecl;
    vd.var = var;
    namespace().addVar(var);
    text = t2;
    return vd;
  } else return null;
}
mixin DefaultParser!(gotVarDecl, "tree.stmt.vardecl");

static this() { parsecon.addPrecedence("tree.expr.arith", "1"); }

Object gotAddSubExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  auto old_op = op;
  retry:
  Expr op2;
  if (t2.accept("+") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("addl")(op, op2);
    goto retry;
  }
  if (t2.accept("-") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("subl")(op, op2);
    goto retry;
  }
  if (op is old_op) return null;
  text = t2;
  return cast(Object) op;
}
mixin DefaultParser!(gotAddSubExpr, "tree.expr.arith.addsub", "1");

Object gotMulDivExpr(ref string text, ParseCb cont, ParseCb rest) {
  Expr op;
  auto t2 = text;
  if (!cont(t2, &op)) return null;
  auto old_op = op;
  retry:
  Expr op2;
  if (t2.accept("*") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("imull")(op, op2);
    goto retry;
  }
  if (t2.accept("/") && cont(t2, &op2)) {
    op = new AsmBinopExpr!("idivl")(op, op2);
    goto retry;
  }
  if (op is old_op) return null;
  text = t2;
  return cast(Object) op;
}
mixin DefaultParser!(gotMulDivExpr, "tree.expr.arith.muldiv", "2");

Object gotCompare(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool not, smaller, equal, greater;
  Expr ex1, ex2;
  if (rest(t2, "tree.expr", &ex1) &&
      (
        (t2.accept("!") && (not = true)),
        (t2.accept("<") && (smaller = true)),
        (t2.accept(">") && (greater = true)),
        ((not || smaller || t2.accept("=")) && t2.accept("=") && (equal = true)),
        (smaller || equal || greater)
      ) && rest(t2, "tree.expr", &ex2)
  ) {
    text = t2;
    return new Compare(ex1, not, smaller, equal, greater, ex2);
  } else return null;
}
mixin DefaultParser!(gotCompare, "tree.cond.compare", "1");

Object gotExprAsCond(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  if (rest(text, "<tree.expr >tree.expr.cond", &ex)) {
    return new Compare(ex, true, false, true, false, new IntExpr(0));
  } else return null;
}
mixin DefaultParser!(gotExprAsCond, "tree.cond.expr", "9");

Object gotExprAsStmt(ref string text, ParseCb cont, ParseCb rest) {
  // TODO: break expr/statement inheritance. it's silly.
  Expr ex;
  auto t2 = text;
  if (rest(t2, "tree.expr", &ex)) {
    text = t2;
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotExprAsStmt, "tree.semicol_stmt.expr");

Object gotWhileStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("while ")) {
    auto ws = new WhileStatement;
    if (rest(t2, "tree.cond", &ws.cond) && rest(t2, "tree.scope", &ws._body)) {
      text = t2;
      return ws;
    } else throw new Exception("Couldn't parse while loop at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotWhileStmt, "tree.stmt.while");

Object gotAssignment(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto as = new Assignment;
  Expr ex;
  if (rest(t2, "tree.expr >tree.expr.arith", &ex) && t2.accept("=")) {
    auto lv = cast(LValue) ex;
    if (!lv) throw new Exception(Format("Assignment target is not an lvalue: ", ex, " at ", t2.next_text()));
    as.target = lv;
    if (rest(t2, "tree.expr", &as.value)) {
      text = t2;
      return as;
    } else throw new Exception("While grabbing assignment value at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotAssignment, "tree.semicol_stmt.assign");

Object gotSemicolStmt(ref string text, ParseCb cont, ParseCb rest) {
  if (auto obj = rest(text, "tree.semicol_stmt")) {
    text.mustAccept(";", "Missing terminating semicolon at '"~text.next_text()~"'");
    return obj;
  } else return null;
}
mixin DefaultParser!(gotSemicolStmt, "tree.stmt.semicolonized");

Object gotForStmt(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("for (")) {
    auto fs = new ForStatement, check = namespace().VarGetCheckpt();
    if (rest(t2, "tree.stmt.vardecl", &fs.decl) &&
        rest(t2, "tree.cond", &fs.cond) && t2.accept(";") &&
        rest(t2, "tree.semicol_stmt", &fs.step) && t2.accept(")") &&
        rest(t2, "tree.scope", &fs._body)
      )
    {
      text = t2;
      namespace().VarSetCheckpt(check);
      return fs;
    } else throw new Exception("Failed to parse for statement at '"~t2.next_text()~"'");
  } else return null;
}
mixin DefaultParser!(gotForStmt, "tree.stmt.for");

Object gotRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("&")) return null;
  
  Expr ex;
  if (!rest(text, "tree.expr >tree.expr.arith", &ex))
    throw new Exception("Address operator found but nothing to take address matched at '"~text.next_text()~"'");
  
  auto lv = cast(LValue) ex;
  if (!lv) throw new Exception(Format("Can't take reference: ", ex, " not an lvalue at ", text.next_text()));
  
  return new RefExpr(lv);
}
mixin DefaultParser!(gotRefExpr, "tree.expr.ref", "31");

Object gotDerefExpr(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("*")) return null;
  
  Expr ex;
  if (!rest(text, "tree.expr >tree.expr.arith", &ex))
    throw new Exception("Dereference operator found but no expression matched at '"~text.next_text()~"'");
  
  return new DerefExpr(ex);
}
mixin DefaultParser!(gotDerefExpr, "tree.expr.deref", "32");

Object gotMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  Expr ex;
  if (!cont(t2, &ex)) return null;
  
  string member;
  
  auto pre_ex = ex;
  while (t2.accept(".") && t2.gotIdentifier(member)) {
    if (!cast(Structure) ex.valueType())
      throw new Exception(Format("Can't access member of non-structure: ", ex, " at ", t2.next_text()));
    
    if (auto lv = cast(LValue) ex)
      ex = new MemberAccess_LValue(lv, member);
    else
      ex = new MemberAccess_Expr(ex, member);
  }
  if (ex is pre_ex) return null;
  else {
    text = t2;
    return cast(Object) ex;
  }
}
mixin DefaultParser!(gotMemberExpr, "tree.expr.member", "35");
