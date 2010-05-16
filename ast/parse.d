module ast.parse;

/**
 ** This is a single module because theoretically,
 ** all parser funs found here can exhibit codependence.
 ** For that reason, and to avoid circular imports,
 ** they have been consolidated.
 **/

import ast.base, ast.namespace, ast.scopes, ast.modules;
import ast.math, ast.cond;
import ast.literals, ast.aggregate, ast.assign, ast.ifstmt;
import ast.fun, ast.returns, ast.variable, ast.jumps, ast.loops;
import ast.pointer, ast.structure;
import tools.base: New, Stuple, stuple;

alias gotExtType gotType;

// alias gotBaseExpr gotMath_Expr; // next on up
alias gotBaseExpr gotDeref_Expr;
alias gotDerefExpr gotRef_Expr;
alias gotRefExpr gotMember_Expr;
alias gotMemberExpr gotMath_Expr;

bool gotRefExpr(ref string text, out Expr ex, Namespace ns) {
  auto t2 = text;
  
  if (!t2.accept("&")) return text.gotRef_Expr(ex, ns);
  if (!t2.gotExpr(ex, ns)) return false;
  
  auto lv = cast(LValue) ex;
  if (!lv) throw new Exception(Format("Can't take reference: ", ex, " not an lvalue at ", t2.next_text()));
  
  text = t2;
  ex = new RefExpr(lv);
  return true;
}

bool gotDerefExpr(ref string text, out Expr ex, Namespace ns) {
  auto t2 = text;
  
  if (!t2.accept("*")) return text.gotDeref_Expr(ex, ns);
  if (!t2.gotExpr(ex, ns)) return false;
  
  text = t2;
  ex = new DerefExpr(ex);
  return true;
}

bool gotMemberExpr(ref string text, out Expr ex, Namespace ns) {
  auto t2 = text;
  logln("try to gotRefExpr off ", t2.next_text());
  if (!t2.gotMember_Expr(ex, ns)) return false;
  string member;
  logln("Getting member expr; left is ", t2.next_text());
  return t2.many(t2.accept(".") && t2.gotIdentifier(member), {
    if (!cast(Structure) ex.valueType())
      throw new Exception(Format("Can't access member of non-structure: ", ex));
    
    if (auto lv = cast(LValue) ex) ex = new MemberAccess_LValue(lv, member);
    else ex = new MemberAccess_Expr(ex, member);
  }) && (text = t2, true);
}

bool gotMathExpr(ref string text, out Expr ex, Namespace ns, int level = 0) {
  auto t2 = text;
  Expr par;
  bool addMath(string op) {
    switch (op) {
      case "+": ex = new AsmBinopExpr!("addl")(ex, par); break;
      case "-": ex = new AsmBinopExpr!("subl")(ex, par); break;
      case "*": ex = new AsmBinopExpr!("imull")(ex, par); break;
      case "/": ex = new AsmBinopExpr!("idivl")(ex, par); break;
    }
    return true;
  }
  switch (level) {
    case -2: return t2.gotMath_Expr(ex, ns) && (text = t2, true);
    case -1:
      return t2.gotMathExpr(ex, ns, level-1) && t2.many(t2.ckbranch(
        t2.accept("*") && t2.gotMathExpr(par, ns, level-1) && addMath("*"),
        t2.accept("/") && t2.gotMathExpr(par, ns, level-1) && addMath("/")
      )) && (text = t2, true);
    case 0:
      return t2.gotMathExpr(ex, ns, level-1) && t2.many(t2.ckbranch(
        t2.accept("+") && t2.gotMathExpr(par, ns, level-1) && addMath("+"),
        t2.accept("-") && t2.gotMathExpr(par, ns, level-1) && addMath("-")
      )) && (text = t2, true);
  }
}

// TODO: rework this properly
alias gotMathExpr gotExpr;

bool gotGenericExpr(ref string text, out Expr ex, Namespace ns) {
  Cond cd;
  return
    text.gotExpr(ex, ns) ||
    text.gotCond(cd, ns) && {
      ex = new CondWrap(cd);
      return true;
    }();
}

bool gotCompare(ref string text, out Cond cd, Namespace ns) {
  auto t2 = text;
  bool not, smaller, equal, greater;
  Expr ex1, ex2;
  return t2.gotExpr(ex1, ns) && (
    (
      (t2.accept("!") && (not = true)),
      (t2.accept("<") && (smaller = true)),
      ((not || smaller || t2.accept("=")) && t2.accept("=") && (equal = true)),
      (t2.accept(">") && (greater = true)),
      (smaller || equal || greater)
    ) && t2.gotExpr(ex2, ns) && {
      cd = new Compare(ex1, not, smaller, equal, greater, ex2);
      text = t2;
      return true;
    }()
    || { cd = new ExprWrap(ex1); text = t2; return true; }()
  );
}

alias gotCompare gotCond;

bool gotFuncall(ref string text, out Expr expr, Namespace ns) {
  auto fc = new FunCall;
  fc.context = ns;
  string t2 = text;
  Expr ex;
  return t2.gotIdentifier(fc.name, true)
    && t2.accept("(")
    && t2.bjoin(t2.gotExpr(ex, ns), t2.accept(","), { fc.params ~= ex; })
    && t2.accept(")")
    && ((text = t2), (expr = fc), true);
}

bool gotScope(ref string text, out Scope sc, Namespace ns) {
  New(sc);
  sc.sup = ns;
  sc.fun = findFun(ns);
  if (text.gotStatement(sc._body, sc)) return true;
  throw new Exception("Couldn't match scope off "~text.next_text());
}

bool gotImportStatement(ref string text, Module mod) {
  string m;
  // import a, b, c;
  return text.accept("import") && text.bjoin(text.gotIdentifier(m, true), text.accept(","), {
    mod.imports ~= lookupMod(m);
  }) && text.accept(";");
}

bool gotStructDef(ref string text, out Structure st, Namespace ns) {
  auto t2 = text;
  if (!t2.accept("struct")) return false;
  string name;
  Structure.Member[] ms;
  // New(st, comps);
  Structure.Member sm;
  return t2.gotIdentifier(name) && t2.accept("{") && t2.many(
    t2.gotType(sm.type, ns) &&
    t2.bjoin(
      t2.gotIdentifier(sm.name),
      t2.accept(",")
      ,{ ms ~= sm; }
    ) &&
    t2.accept(";")
  ) && t2.accept("}")
    && (New(st, name, ms), text = t2, true);
}

bool gotModule(ref string text, out Module mod) {
  auto t2 = text;
  Function fn;
  Structure st;
  Tree tr;
  return t2.accept("module ") && (New(mod), true) &&
    t2.gotIdentifier(mod.name, true) && t2.accept(";") &&
    t2.many(
      t2.gotFunDef(fn, mod) && (tr = fn, true) ||
      t2.gotStructDef(st, mod) && (mod.addStruct(st), tr = null, true) ||
      t2.gotImportStatement(mod) && (tr = null, true),
    {
      if (tr) mod.entries ~= tr;
    }) && (text = t2, true);
}

bool gotBaseExpr(ref string text, out Expr expr, Namespace ns) {
  Variable var;
  int i;
  return
       text.gotFuncall(expr, ns)
    || text.gotStringExpr(expr)
    || text.gotIntExpr(expr)
    || text.gotVariable(var, ns) && (expr = var, true)
    || { auto t2 = text; return t2.accept("(") && t2.gotGenericExpr(expr, ns) && t2.accept(")") && (text = t2, true); }();
}

bool gotRetStmt(ref string text, out ReturnStmt rs, Namespace ns) {
  auto t2 = text;
  return
    t2.accept("return") && (New(rs), rs.ns = ns, true) &&
    t2.gotExpr(rs.value, ns) && (text = t2, true);
}

import tools.compat: rfind;
bool gotVariable(ref string text, out Variable v, Namespace ns) {
  // logln("Match variable off ", text.next_text());
  string name, t2 = text;
  return t2.gotIdentifier(name, true)
    && {
      logln("Look for ", name, " in ", ns.Varfield);
      retry:
      if (auto res = ns.lookupVar(name)) {
        v = res;
        if (!text.accept(name)) throw new Exception("WTF! "~name~" at "~text.next_text());
        return true;
      }
      if (name.rfind(".") != -1) {
        name = name[0 .. name.rfind(".")];
        goto retry;
      }
      error = "unknown identifier "~name;
      return false;
    }();
}

bool gotSemicolonizedStatement(ref string text, out Statement stmt, Namespace ns) {
  Expr ex; ReturnStmt rs; GotoStmt gs;
  Assignment ass; VarDecl vd;
  auto t2 = text;
  return
    (text.gotRetStmt(rs, ns) && (stmt = rs, true)) ||
    (text.gotGotoStmt(gs, ns) && (stmt = gs, true)) ||
    (text.gotAssignment(ass, ns) && (stmt = ass, true)) ||
    (text.gotVarDecl(vd, ns) && (stmt = vd, true)) ||
    (t2.gotExpr(ex, ns) && (text = t2, stmt = ex, true)) // least grubby
  ;
}

bool gotStatement(ref string text, out Statement stmt, Namespace ns, bool needSemicolon = true) {
  AggrStatement as;
  VarDecl vd; Assignment ass; ForStatement fs;
  IfStatement ifs; ReturnStmt rs;
  Label l; GotoStmt gs; WhileStatement ws;
  auto t2 = text;
  return
    (text.gotAggregateStmt(as, ns) && (stmt = as, true)) ||
    (text.gotIfStmt(ifs, ns) && (stmt = ifs, true)) ||
    (text.gotLabel(l, ns) && (stmt = l, true)) ||
    (text.gotWhileStmt(ws, ns) && (stmt = ws, true)) ||
    (text.gotForStmt(fs, ns) && (stmt = fs, true)) ||
    (t2.gotSemicolonizedStatement(stmt, ns)
      && (!needSemicolon || t2.accept(";"))
      && (text = t2, true))
    ;
}

bool gotFunDef(ref string text, out Function fun, Module mod) {
  Type ptype;
  string t2 = text;
  New(fun);
  New(fun.type);
  string parname;
  error = null;
  return
    t2.gotType(fun.type.ret, mod)
    && t2.gotIdentifier(fun.name)
    && t2.accept("(")
    // TODO: function parameters belong on the stackframe
    && t2.bjoin(t2.gotType(ptype, mod) && (t2.gotIdentifier(parname) || ((parname=null), true)), t2.accept(","), {
      fun.type.params ~= stuple(ptype, parname);
    })
    && t2.accept(")")
    && (fun.sup = mod, fun.fixup, true)
    && t2.gotScope(fun._scope, fun)
    && ((text = t2), (mod.addFun(fun), true))
    ;
}

bool gotVarDecl(ref string text, out VarDecl vd, Namespace ns) {
  auto t2 = text;
  auto var = new Variable;
  Expr iv;
  return
    t2.gotType(var.type, ns)
    && t2.gotIdentifier(var.name)
    && (t2.accept("=") && t2.gotExpr(iv, ns) && {
      var.initval = iv;
      return true;
    }() || true)
    && {
      var.baseOffset =
        -(cast(Scope) ns).framesize() - var.type.size; // TODO: check
      New(vd);
      vd.var = var;
      ns.addVar(var);
      text = t2;
      return true;
    }();
}

bool gotAggregateStmt(ref string text, out AggrStatement as, Namespace ns) {
  auto t2 = text;
  
  Statement st;
  return t2.accept("{") && (as = new AggrStatement, true) &&
    t2.many(t2.gotStatement(st, ns), { as.stmts ~= st; })
    && t2.mustAccept("}", Format("Encountered unknown statement at ", t2.next_text()))
    && (text = t2, true);
}

import tools.log;
bool gotAssignment(ref string text, out Assignment as, Namespace ns) {
  auto t2 = text;
  New(as);
  Expr ex;
  logln("get assign off ", t2.next_text());
  return t2.gotExpr(ex, ns) && t2.accept("=") && {
    auto lv = cast(LValue) ex;
    if (!lv) throw new Exception(Format("Assignment target is not an lvalue: ", ex, " at ", t2.next_text()));
    as.target = lv;
    return true;
  }() && t2.gotExpr(as.value, ns) && {
    text = t2;
    return true;
  }();
}

bool gotIfStmt(ref string text, out IfStatement ifs, Namespace ns) {
  auto t2 = text;
  return
    t2.accept("if") && (New(ifs), true) &&
    t2.gotCond(ifs.test, ns) && t2.gotScope(ifs.branch1, ns) && (
      t2.accept("else") && t2.gotScope(ifs.branch2, ns)
      || true
    ) && (text = t2, true);
}

bool gotGotoStmt(ref string text, out GotoStmt gs, Namespace ns) {
  auto t2 = text;
  return
    t2.accept("goto") && (New(gs), true) && t2.gotIdentifier(gs.target) && (text = t2, true);
}

bool gotWhileStmt(ref string text, out WhileStatement ws, Namespace ns) {
  auto t2 = text;
  return
    t2.accept("while") && (New(ws), true) &&
    t2.gotCond(ws.cond, ns) && t2.gotScope(ws._body, ns) &&
    (text = t2, true);
}

bool gotForStmt(ref string text, out ForStatement fs, Namespace ns) {
  auto t2 = text;
  typeof(ns.VarGetCheckpt()) check;
  return
    t2.accept("for (") && {
      New(fs);
      check = ns.VarGetCheckpt();
      return true;
    }() && (
        t2.gotVarDecl(fs.decl, ns)
      && t2.accept(";")
      && t2.gotCond(fs.cond, ns)
      && t2.accept(";")
      && t2.gotStatement(fs.step, ns, false)
      && t2.accept(")")
      && t2.gotScope(fs._body, ns)
      && (text = t2, ns.VarSetCheckpt(check), true)
      || {
        throw new Exception(
          "Unable to match for statement; stumbled over " ~ t2.next_text());
        return true;
      }()
    );
}

bool gotLabel(ref string text, out Label l, Namespace ns) {
  auto t2 = text;
  New(l);
  return t2.gotIdentifier(l.name) && t2.accept(":") && (text = t2, true);
}

bool gotBasicType(ref string text, out Type type, Namespace ns) {
  if (text.accept("void")) return type = Single!(Void), true;
  if (text.accept("size_t")) return type = Single!(SizeT), true;
  if (text.accept("int")) return type = Single!(SysInt), true;
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    if (auto st = ns.lookupStruct(id)) {
      type = st;
      text = t2;
      return true;
    }
  }
  return false;
}

bool gotExtType(ref string text, out Type type, Namespace ns) {
  if (!text.gotBasicType(type, ns)) return false;
  restart:
  foreach (dg; typeModlist) {
    if (auto nt = dg(text, type)) {
      type = nt;
      goto restart;
    }
  }
  return true;
}
