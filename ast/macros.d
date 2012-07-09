module ast.macros;

import ast.tenth;
import parseBase, ast.base, ast.literal_string, ast.tuples, ast.fun, ast.funcall,
       ast.namespace, ast.tuple_access, ast.variable, ast.vardecl, ast.scopes,
       ast.aggregate, ast.assign, ast.ifstmt, ast.literals, ast.pointer, ast.casting,
       ast.opers, ast.conditionals, ast.returns, ast.nulls;

import tools.base: This;

class Swap : Statement {
  LValue lv1, lv2;
  MValue mv1, mv2;
  int sz;
  this(LValue lv1, LValue lv2) {
    this.lv1 = lv1;
    this.lv2 = lv2;
    auto vt1 = lv1.valueType(), vt2 = lv2.valueType();
    if (vt1 != vt2) {
      logln("halt: swap(", lv1, ", ", lv2, ")");
      fail;
    }
    sz = vt1.size;
  }
  this(MValue mv1, MValue mv2) {
    this.mv1 = mv1;
    this.mv2 = mv2;
    auto vt1 = mv1.valueType(), vt2 = mv2.valueType();
    if (vt1 != vt2) {
      logln("halt: swap(", mv1, ", ", mv2, ")");
      fail;
    }
    sz = vt1.size;
  }
  mixin defaultIterate!(lv1, lv2, mv1, mv2);
  override {
    Swap dup() {
      if (mv1) return fastalloc!(Swap)(mv1.dup, mv2.dup);
      else return fastalloc!(Swap)(lv1.dup, lv2.dup);
    }
    void emitAsm(AsmFile af) {
      if (mv1) {
        mv1.emitAsm(af);
        mv2.emitAsm(af);
        mv1.emitAssignment(af);
        mv2.emitAssignment(af);
        return;
      }
      lv1.emitLocation(af);
      lv2.emitLocation(af);
      af.popStack("%eax", 4);
      af.popStack("%ebx", 4);
      int sz = sz;
      int offs;
      if (sz % 4 == 0) {
        while (sz) {
          af.mmove4(qformat(offs, "(%eax)"[]), "%ecx");
          af.mmove4(qformat(offs, "(%ebx)"[]), "%edx");
          af.mmove4("%ecx", qformat(offs, "(%ebx)"[]));
          af.mmove4("%edx", qformat(offs, "(%eax)"[])); // faster than af.swap!
          offs += 4;
          sz -= 4;
        }
      } else {
        while (sz) {
          af.mmove1(qformat(offs, "(%eax)"[]), "%cl");
          af.mmove1(qformat(offs, "(%ebx)"[]), "%dl");
          af.mmove1("%cl", qformat(offs, "(%ebx)"[]));
          af.mmove1("%dl", qformat(offs, "(%eax)"[])); // faster than af.swap!
          offs ++;
          sz --;
        }
      }
      af.nvm("%eax");
      af.nvm("%ebx");
    }
  }
}

extern(C) void fcc_initTenth() {
  if (rootctx) return;
  rootctx = new Context;
  rootctx.add("nil", NilEnt);
  rootctx.add("t", NonNilEnt);
  rootctx.add("last", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    return args[$-1];
  }));
  rootctx.add("def", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Too many arguments to def: 2 expected");
    mixin(chaincast("tok: First arg to def: args[0]->Token: %.name"));
    ctx.add(tok, args[1]);
    return args[1];
  }));
  rootctx.add("flatten", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    Entity[] res;
    void handle(Entity ent) {
      if (auto list = fastcast!(List) (ent))
        foreach (entry; list.entries) handle(entry);
      else
        res ~= ent;
    }
    foreach (arg; args) handle(arg);
    return fastalloc!(List)(res);
  }));
  rootctx.add("assert", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'assert': 1 expected");
    if (isNil(args[0]))
      tnte("Assert violated");
    return args[0];
  }));
  rootctx.add("make-tuple-expr", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to make-tuple-expr: 1 expected");
    mixin(chaincast("list: Argument to make-tuple-expr: args[0]->List"));
    Expr[] exlist = new Expr[list.entries.length];
    foreach (i, e; list.entries) {
      mixin(chaincast("ex: List entry for make-tuple-expr: e->ItrEntity: %.itr->Expr"));
      exlist[i] = ex;
    }
    return fastalloc!(ItrEntity)(mkTupleExpr(exlist));
  }));
  rootctx.add("make-call", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to make-call: 2 expected");
    mixin(chaincast("fun: First arg for make-call: args[0]->ItrEntity: %.itr->Function"));
    mixin(chaincast("ex: Second arg for make-call: args[1]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(buildFunCall(fun, ex, "tenth-call"));
  }));
  rootctx.add("make-exprwrap", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-exprwrap': 1 expected");
    mixin(chaincast("ex: Arg for 'make-exprwrap': args[0]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(fastalloc!(ExprWrap)(ex));
  }));
  rootctx.add("make-int", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-int': 1 expected");
    mixin(chaincast("num: First arg for 'make-int': args[0]->Integer: %.value"));
    return fastalloc!(ItrEntity)(mkInt(num));
  }));
  rootctx.add("make-swap", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-swap': 2 expected");
    mixin(chaincast("arg1:  First arg to 'make-swap': args[0]->ItrEntity: %.itr"));
    mixin(chaincast("arg2: Second arg to 'make-swap': args[1]->ItrEntity: %.itr"));
    auto lv1 = fastcast!(LValue)(arg1), lv2 = fastcast!(LValue)(arg2);
    if (lv1 && lv2) return fastalloc!(ItrEntity)(fastalloc!(Swap)(lv1, lv2));
    auto mv1 = fastcast!(MValue)(arg1), mv2 = fastcast!(MValue)(arg2);
    if (mv1 && mv2) return fastalloc!(ItrEntity)(fastalloc!(Swap)(mv1, mv2));
    tnte("arguments to make-swap must be lv, lv or mv, mv");
  }));
  rootctx.add("make-string", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-string': 1 expected");
    mixin(chaincast("str: First arg for 'make-string': args[0]->Token: %.name"));
    return fastalloc!(ItrEntity)(mkString(str));
  }));
  rootctx.add("make-or", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-or': 2 expected");
    mixin(chaincast("cd1: First arg for 'make-or': args[0]->ItrEntity: %.itr->Cond"));
    mixin(chaincast("cd2: Second arg for 'make-or': args[1]->ItrEntity: %.itr->Cond"));
    return fastalloc!(ItrEntity)(fastalloc!(OrOp)(cd1, cd2));
  }));
  rootctx.add("make-and", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-and': 2 expected");
    mixin(chaincast("cd1: First arg for 'make-and': args[0]->ItrEntity: %.itr->Cond"));
    mixin(chaincast("cd2: Second arg for 'make-and': args[1]->ItrEntity: %.itr->Cond"));
    return fastalloc!(ItrEntity)(fastalloc!(AndOp)(cd1, cd2));
  }));
  rootctx.add("make-if", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-if': 2 expected");
    mixin(chaincast("it: First arg for 'make-if': args[0]->ItrEntity: %.itr"));
    Cond cd = fastcast!(Cond) (it);
    if (!cd) {
      mixin(chaincast("ex: First arg (cond or expr) for 'make-if': it->Expr"));
      cd = testNonzero(ex);
    }
    auto ifs = new IfStatement;
    ifs.wrapper = new Scope;
    ifs.wrapper.requiredDepthDebug ~= " (ast.macros:144)";
    ifs.test = cd;
    namespace.set(ifs.wrapper);
    
    auto branch1 = new Scope;
    ifs.branch1 = branch1;
    branch1.requiredDepthDebug ~= " (ast.macros:150)";
    namespace.set(branch1);
    
    scope(exit) namespace.set(ifs.wrapper.sup);
    
    mixin(chaincast("st: Second arg for 'make-if', evaluated: args[1].eval(ctx)->ItrEntity: %.itr->Statement"));
    branch1.addStatement(st);
    
    return fastalloc!(ItrEntity)(ifs);
  }));
  rootctx.add("make-return", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-return': 1 expected");
    mixin(chaincast("ex: Arg for 'make-return': args[0]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(fastalloc!(ReturnStmt)(ex));
  }));
  rootctx.add("substitute", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to 'substitute': 3 expected");
    mixin(chaincast("itr: First arg for 'substitute': args[0]->ItrEntity: %.itr"));
    mixin(chaincast("from: Second arg for 'substitute': args[1]->ItrEntity: %.itr"));
    mixin(chaincast("to: Third arg for 'substitute': args[2]->ItrEntity: %.itr"));
    auto efrom = fastcast!(Expr)(from), eto = fastcast!(Expr)(to);
    if (efrom && eto && efrom.valueType() != eto.valueType())
      tnte("Cannot substitute ", from, " with ", to, ": mismatched types");
    void subst(ref Iterable it) {
      if (it == from) it = to;
      it.iterate(&subst);
    }
    itr = itr.dup();
    subst(itr);
    return fastalloc!(ItrEntity)(itr);
  }));
  rootctx.add("lookup", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to lookup: 1 expected");
    mixin(chaincast("tok: Arg for lookup: args[0]->Token: %.name"));
    auto res = fastcast!(Tree) (namespace().lookup(tok));
    if (!res) tnte("No such object: ", tok);
    return fastalloc!(ItrEntity)(res);
  }));
  rootctx.add("not", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'not': 1 expected");
    if (isNil(args[0])) return NonNilEnt;
    else return NilEnt;
  }));
  rootctx.add("or", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'or': >=1 expected");
    bool res = false;
    foreach (arg; args) res |= !isNil(arg);
    if (res) return NonNilEnt;
    else return NilEnt;
  }));
  rootctx.add("and", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'and': >=1 expected");
    bool res = true;
    foreach (arg; args) res &= !isNil(arg);
    if (res) return NonNilEnt;
    else return NilEnt;
  }));
  rootctx.add("add", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'add': >=1 expected");
    int res;
    foreach (arg; args) {
      mixin(chaincast("val: Arg to 'add': arg->Integer: %.value"));
      res += val;
    }
    return fastalloc!(Integer)(res);
  }));
  rootctx.add("sub", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'sub': >=1 expected");
    mixin(chaincast("res: First arg to 'sub': args[0]->Integer: %.value"));
    foreach (arg; args[1..$]) {
      mixin(chaincast("val: Arg to 'sub': arg->Integer: %.value"));
      res -= val;
    }
    return fastalloc!(Integer)(res);
  }));
  rootctx.add("mul", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'mul': >=1 expected");
    int res = 1;
    foreach (arg; args[1..$]) {
      mixin(chaincast("val: Arg to 'mul': arg->Integer: %.value"));
      res *= val;
    }
    return fastalloc!(Integer)(res);
  }));
  rootctx.add("div", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (!args.length) tnte("Wrong number of args to 'mul': >=1 expected");
    mixin(chaincast("res: First arg to 'div': args[0]->Integer: %.value"));
    foreach (arg; args[1..$]) {
      mixin(chaincast("val: Arg to 'div': arg->Integer: %.value"));
      res /= val;
    }
    return fastalloc!(Integer)(res);
  }));
  rootctx.add("mod", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'mod': 2 expected (int, int), not ", args);
    mixin(chaincast("v1:  First arg to 'mod': args[0]->Integer: %.value"));
    mixin(chaincast("v2: Second arg to 'mod': args[1]->Integer: %.value"));
    return fastalloc!(Integer)(v1%v2);
  }));
  rootctx.add("equal", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'equal': 2 expected (int, int), not ", args);
    mixin(chaincast("v1:  First arg to 'mod': args[0]->Integer: %.value"));
    mixin(chaincast("v2: Second arg to 'mod': args[1]->Integer: %.value"));
    if (v1 != v2) return NilEnt;
    return NonNilEnt;
  }));
  rootctx.add("eval", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'eval': 1 expected");
    return args[0].eval(ctx);
  }));
  rootctx.add("if", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 3) tnte("Wrong number of args to 'if': 3 expected");
    auto cond = args[0];
    bool bcond = !isNil(cond);
    if (bcond) return args[1].eval(ctx);
    else return args[2].eval(ctx);
  }));
  rootctx.add("make-temporary", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-temporary': 1 expected");
    mixin(chaincast("ty: Arg for make-temporary: args[0]->TypeEntity: %.ty"));
    auto var = fastalloc!(Variable)(ty, cast(string) null, boffs(ty));
    var.dontInit = true;
    auto sc = namespace().get!(Scope);
    sc.add(var);
    sc.addStatement(fastalloc!(VarDecl)(var));
    return fastalloc!(ItrEntity)(var);
  }));
  rootctx.add("type-of", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'type-of': 1 expected");
    mixin(chaincast("ty: Arg for type-of: args[0]->ItrEntity: %.itr->Expr: %.valueType()"));
    return fastalloc!(TypeEntity)(ty);
  }));
  rootctx.add("types-equal", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'types-equal': 2 expected");
    mixin(chaincast("ty1:  First arg for 'types-equal': args[0]->TypeEntity: %.ty"));
    mixin(chaincast("ty2: Second arg for 'types-equal': args[1]->TypeEntity: %.ty"));
    if (ty1 != ty2) return NilEnt;
    return NonNilEnt;
  }));
  rootctx.add("basic-type", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'basic-type': 1 expected, type name");
    mixin(chaincast("name: Arg for 'basic-type': args[0]->Token: %.name"));
    mixin(BasicTypeTable.ctTableUnroll(`
      if (name == "$name") return fastalloc!(TypeEntity)(Single!($type));
    `));
    return NilEnt;
  }));
  rootctx.add("make-sae", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-sae': 2 expected");
    mixin(chaincast("st: First arg for make-sae: args[0]->ItrEntity: %.itr->Statement"));
    mixin(chaincast("ex: Second arg for make-sae: args[1]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(mkStatementAndExpr(st, ex));
  }));
  rootctx.add("make-reference", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-reference': 1 expected, Expr");
    mixin(chaincast("cv: Arg to 'make-reference': args[0]->ItrEntity: %.itr->CValue"));
    return fastalloc!(ItrEntity)(fastalloc!(RefExpr)(cv));
  }));
  rootctx.add("make-deref", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-deref': 1 expected, Expr");
    mixin(chaincast("ex: Arg to 'make-deref': args[0]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(fastalloc!(DerefExpr)(ex));
  }));
  rootctx.add("make-aggregate", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-aggregate': 1 expected (list), not ", args);
    mixin(chaincast("list: Arg for make-aggregate: args[0]->List"));
    auto res = new AggrStatement;
    foreach (ent; list.entries) {
      mixin(chaincast("st: List entry for make-aggregate: ent->ItrEntity: %.itr->Statement"));
      res.stmts ~= st;
    }
    return fastalloc!(ItrEntity)(res);
  }));
  rootctx.add("reinterpret-cast", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'reinterpret-cast': 2 expected (type, expr), not ", args);
    mixin(chaincast("ty:  First arg to 'reinterpret-cast': args[0]->TypeEntity: %.ty"));
    mixin(chaincast("ex: Second arg to 'reinterpret-cast': args[1]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(reinterpret_cast(ty, ex));
  }));
  rootctx.add("pointer-to", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'pointer-to': 1 expected (type)");
    mixin(chaincast("ty: Arg to 'pointer-to': args[0]->TypeEntity: %.ty"));
    return fastalloc!(TypeEntity)(fastalloc!(Pointer)(ty));
  }));
  rootctx.add("size-of", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'size-of': 1 expected (type)");
    mixin(chaincast("ty: Arg to 'pointer-to': args[0]->TypeEntity: %.ty"));
    return fastalloc!(Integer)(ty.size());
  }));
  rootctx.add("make-add", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-add': 2 expected (expr, expr), not ", args);
    mixin(chaincast("ex1:  First arg to 'make-add': args[0]->ItrEntity: %.itr->Expr"));
    mixin(chaincast("ex2: Second arg to 'make-add': args[1]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(lookupOp("+", ex1, ex2));
  }));
  rootctx.add("make-assignment", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-assignment': 2 expected");
    mixin(chaincast("dest: First arg for make-assignment: args[0]->ItrEntity: %.itr->Expr"));
    mixin(chaincast("src: Second arg for make-assignment: args[1]->ItrEntity: %.itr->Expr"));
    return fastalloc!(ItrEntity)(mkAssignment(dest, src));
  }));
  rootctx.add("make-placeholder", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'make-placeholder': 1 expected");
    mixin(chaincast("type: Arg for make-placeholder: args[0]->TypeEntity: %.ty"));
    return fastalloc!(ItrEntity)(fastalloc!(PlaceholderToken)(type, "Tenth macro placeholder"));
  }));
  rootctx.add("make-tuple-index", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'make-tuple-index': 2 expected");
    mixin(chaincast("tup: First arg for make-tuple-index: args[0]->ItrEntity: %.itr->Expr"));
    mixin(chaincast("index: Second arg for make-tuple-index: args[1]->Integer: %.value"));
    return fastalloc!(ItrEntity)(mkTupleIndexAccess(tup, index));
  }));
  rootctx.add("with-scope", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'with-scope': 1 expected");
    auto sc = new Scope;
    sc.requiredDepthDebug ~= " (ast.macros:with-scope)";
    namespace.set(sc);
    scope(exit) namespace.set(sc.sup);
    auto thing = args[0].eval(ctx);
    mixin(chaincast("st: Result of with-scope arg0: thing->ItrEntity: %.itr -> Statement"));
    sc.addStatement(st);
    return fastalloc!(ItrEntity)(sc);
  }));
  rootctx.add("insert-scope", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'insert-scope': 2 expected");
    mixin(chaincast("name: First arg for 'insert-scope': args[0]->Token: %.name"));
    mixin(chaincast("tr: Second arg for 'insert-scope': args[1]->ItrEntity: %.itr"));
    namespace().add(name, tr);
    return args[1];
  }));
  rootctx.add("remove-scope", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'remove-scope': 1 expected");
    mixin(chaincast("name: First arg for 'remove-scope': args[0]->Token: %.name"));
    
    auto ns = namespace();
    typeof(ns.field) res;
    foreach (pair; ns.field) {
      if (pair._0 != name) res ~= pair;
    }
    ns.field = res;
    ns.rebuildCache;
    return NonNilEnt;
  }));
  rootctx.add("list", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    return fastalloc!(List)(args);
  }));
  rootctx.add("index", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'index': 2 expected: list and index");
    mixin(chaincast("list: First arg to 'length': args[0]->List"));
    mixin(chaincast("index: Second arg to 'length': args[1]->Integer"));
    auto iv = index.value, le = list.entries;
    if (iv < 0 || iv >= le.length)
      tnte("Bad index: (index ", list, " ", iv, ")");
    return le[iv];
  }));
  rootctx.add("length", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'length': 1 expected");
    mixin(chaincast("len: Arg to 'length': args[0]->List: %.entries.length"));
    return fastalloc!(Integer)(len);
  }));
  rootctx.add("tuple-length", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'tuple-length': 1 expected");
    mixin(chaincast("len: Arg to 'tuple-length': args[0]->ItrEntity: %.itr->Expr: resolveType(%.valueType())->Tuple: %.types.length"));
    return fastalloc!(Integer)(len);
  }));
  rootctx.add("is-tuple", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'is-tuple': 1 expected");
    mixin(chaincast("ty: Arg to 'is-tuple': args[0]->ItrEntity: %.itr->Expr: resolveType(%.valueType())"));
    return (!!fastcast!(Tuple) (ty))?NonNilEnt:NilEnt;
  }));
  rootctx.add("tuple-exprs", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of args to 'tuple-exprs': 1 expected");
    mixin(chaincast("exprs: Arg to 'tuple-exprs': args[0]->ItrEntity: %.itr->Expr: getTupleEntries(%)"));
    auto list = new Entity[exprs.length];
    foreach (i, ex; exprs) list[i] = fastalloc!(ItrEntity)(ex);
    return fastalloc!(List)(list);
  }));
  rootctx.add("for", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
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
        loopct.add(ident, fastalloc!(Integer)(i));
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
    return fastalloc!(List)(res);
  }));
  rootctx.add("while", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'while': 2 expected");
    Entity[] res;
    while (!isNil(args[0].eval(ctx)))
      res ~= args[1].eval(ctx);
    return fastalloc!(List)(res);
  }));
  rootctx.add("lambda", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 2) tnte("Wrong number of args to 'lambda': 2 expected");
    return fastalloc!(DgCallable)(stuple(ctx, args) /apply/
      delegate Entity(Context prevctx, Entity[] prevargs, Context ctx, Entity[] args) {
        mixin(chaincast("paramlist: Parameter list for 'lambda': prevargs[0]->List: %.entries"));
        if (paramlist.length != args.length)
          tnte("Invalid number of parameters to lambda ", prevargs, ": ", args);
        auto innerctx = fastalloc!(Context)(prevctx);
        foreach (i, par; paramlist) {
          mixin(chaincast("name: Argument declaration for 'lambda': par->Token: %.name"));
          innerctx.add(name, args[i]);
        }
        return prevargs[1].eval(innerctx);
      }
    );
  }));
}

import ast.modules;
Object runTenth(Object obj, ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto mac = fastcast!(TenthMacro) (obj);
  // imports can be found in functions ..
  auto fun = namespace().get!(Function);
  Object findme;
  if (fun) { findme = fun.lookup(mac.identifier, false); }
  if (!findme) {
    // .. and modules.
    auto mod = namespace().get!(Module);
    if (!mod) return null; // iparse, probably - no need for macros
    findme = mod.lookup(mac.identifier, false);
  }
  if (findme !is mac) return null; // check if we're in scope
  if (mac.key && !t2.accept(mac.key)) return null;
  auto ent = mac.root;
  fcc_initTenth;
  auto ctx = fastalloc!(Context)(rootctx);
  ctx.add("failparse", new DgCallable(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'failparse': 1 expected");
    mixin(chaincast("str: First argument for 'failparse': args[0]->Token: %.name"));
    logln("meep");
    logln(t2.nextText());
    t2.failparse(str);
    assert(false);
  }));
  ctx.add("parse-ident", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-ident: 0 expected");
    string ident;
    if (!t2.gotIdentifier(ident))
      t2.failparse("Identifier expected");
    return fastalloc!(Token)(ident);
  }));
  ctx.add("parse-tuple", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-tuple: 0 expected");
    Expr tup;
    if (!rest(t2, "tree.expr _tree.expr.arith", &tup)
     || !fastcast!(Tuple) (resolveType(tup.valueType())))
      t2.failparse("Tuple expected");
    return fastalloc!(ItrEntity)(tup);
  }));
  ctx.add("parse-expr", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 0 && args.length != 1) tnte("Too many arguments to parse-expr: 0 or 1 (string) expected");
    Expr ex;
    string match = "tree.expr";
    if (args.length == 1) {
      mixin(chaincast("m: Argument to parse-expr: args[0]->Token: %.name"));
      match = m;
    }
    if (!rest(t2, match, &ex)) t2.failparse("Expression expected");
    return fastalloc!(ItrEntity)(ex);
  }));
  ctx.add("is-lvalue", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'is-lvalue': 1 expected");
    mixin(chaincast("ex: First argument for 'is-lvalue': args[0]->ItrEntity: %.itr"));
    if (fastcast!(LValue) (ex)) return NonNilEnt;
    else return NilEnt;
  }));
  ctx.add("is-mvalue", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'is-mvalue': 1 expected");
    mixin(chaincast("ex: First argument for 'is-mvalue': args[0]->ItrEntity: %.itr"));
    if (fastcast!(MValue) (ex)) return NonNilEnt;
    else return NilEnt;
  }));
  ctx.add("parse-stmt", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-stmt: 0 expected");
    Statement st;
    if (!rest(t2, "tree.stmt", &st)) t2.failparse("Statement expected");
    return fastalloc!(ItrEntity)(st);
  }));
  ctx.add("parse-cond", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to parse-cond: 0 expected");
    Cond cd;
    if (!rest(t2, "cond", &cd)) t2.failparse("Condition expected");
    configure(cd);
    return fastalloc!(ItrEntity)(cd);
  }));
  ctx.add("parse-type", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length) tnte("Too many arguments to 'parse-type': 0 expected");
    IType ty;
    if (!rest(t2, "type", &ty))
      t2.failparse("Type expected");
    return fastalloc!(TypeEntity)(ty);
  }));
  ctx.add("matched-text", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'matched-text': 1 expected");
    mixin(chaincast("tok: Argument to matched-text: args[0]->Token: %.name"));
    if (!t2.accept(tok)) {
      return NilEnt;
    }
    return NonNilEnt;
  }));
  ctx.add("match-text", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'match-text': 1 expected");
    mixin(chaincast("tok: Argument to 'match-text': args[0]->Token: %.name"));
    if (!t2.accept(tok)) {
      t2.failparse("Expected \"", tok, "\"");
    }
    return NonNilEnt;
  }));
  string[] sourcestack;
  ctx.add("pushed-source", fastalloc!(DgCallable)(delegate Entity(Context ctx, Entity[] args) {
    if (args.length != 1) tnte("Wrong number of arguments to 'pushed-source': 1 expected");
    mixin(chaincast("list: Argument to 'pushed-source': args[0]->List"));
    sourcestack ~= t2;
    auto res = list.eval(ctx);
    t2 = sourcestack[$-1];
    sourcestack = sourcestack[0..$-1];
    return res;
  }));
  auto res = ent.eval(ctx);
  if (isNil(res)) return null;
  auto ie = fastcast!(ItrEntity) (res);
  if (!ie) tnte("Macro must evaluate to tree, not ", res);
  text = t2;
  return fastcast!(Object) (ie.itr);
}

Object gotMacroStmt(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("("[])) text.failparse("Opening paren expected. ");
  StringExpr rulename, ruleid, prematch;
  if (!rest(text, "tree.expr _tree.expr.arith"[], &rulename))
    text.failparse("Rule name expected");
  if (!text.accept(","[]))
    text.failparse("Comma expected");
  if (!rest(text, "tree.expr _tree.expr.arith"[], &ruleid))
    text.failparse("Rule ID expected");
  if (text.accept(","[])) {
    if (!rest(text, "tree.expr _tree.expr.arith"[], &prematch))
      text.failparse("Pre-match string expected");
  }
  if (!text.accept(")"[]))
    text.failparse("Closing paren expected. ");
  StringExpr src;
  if (!rest(text, "tree.expr _tree.expr.arith"[], &src))
    text.failparse("Expected source string");
  if (!text.accept(";"[]))
    text.failparse("Closing semicolon expected");
  Object obj;
  {
    auto s2 = src.str;
    auto ent = parseTenth(s2);
    auto mac = fastalloc!(TenthMacro)(ent, prematch?prematch.str:null);
    obj = mac;
  }
  auto parser = (new DefaultParserImpl!(runTenth, null, true, null)(obj)).genParser();
  parser.id = rulename.str;
  if (prematch)
    parser.key = prematch.str;
  parsecon.addParser(parser, ruleid.str);
  return obj;
}
mixin DefaultParser!(gotMacroStmt, "tree.toplevel.a_macro", null, "macro"); // sort first because is cheap to exclude
