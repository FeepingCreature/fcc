module ast.conditional_opt;

import ast.base, ast.conditionals, ast.static_arrays, ast.fold;
import ast.int_literal, ast.math, ast.casting, ast.pointer, ast.variable, ast.assign, ast.tuples;

static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto ew = fastcast!(ExprWrap) (it);
    if (!ew) return null;
    auto ce = fastcast!(CondExpr) (ew.ex);
    if (!ce) return null;
    return ce.cd;
  };
  foldopt ~= delegate Itr(Itr it) {
    auto ce = fastcast!(CondExpr) (it);
    if (!ce) return null;
    auto ew = fastcast!(ExprWrap) (ce.cd);
    if (!ew) return null;
    return ew.ex;
  };
  foldopt ~= delegate Itr(Itr it) {
    Expr subtransform(Iterable nit) {
      auto lvamv = fastcast!(LValueAsMValue) (nit);
      if (lvamv) nit = lvamv.sup;
      
      auto de = fastcast!(DerefExpr) (nit);
      if (!de) return null;
      auto rcp = fastcast!(RCE) (de.src);
      if (!rcp) return null;
      
      auto aibe = fastcast!(AsmIntBinopExpr) (rcp.from);
      if (!aibe) return null;
      auto rci = fastcast!(RCE) (aibe.e1);
      if (!rci || Single!(SysInt) != rci.to) return null;
      
      auto aibe2 = fastcast!(AsmIntBinopExpr) (aibe.e2);
      if (!aibe2 || aibe2.op != "*"[]) return null;
      auto mulie = fastcast!(IntExpr) (aibe2.e2);
      if (!mulie || mulie.num != 4) return null;
      auto ic = fastcast!(RCE) (aibe2.e1);
      if (!ic || Single!(SysInt) != ic.to) return null;
      auto ce = fastcast!(CondExpr) (ic.from);
      if (!ce) return null;
      
      auto re = fastcast!(RefExpr) (rci.from);
      if (!re) return null;
      auto sal = fastcast!(StatementAndLValue) (re.src);
      if (!sal) return null;
      auto var = fastcast!(Variable) (sal.second);
      if (!var) return null;
      auto as = fastcast!(Assignment) (sal.first);
      if (!as || as.target !is var) return null;
      auto salit = fastcast!(SALiteralExpr) (as.value);
      
      if (salit.exs.length != 2) return null;
      if (salit.exs[0].valueType().size != 4 || salit.exs[1].valueType().size != 4)
        return null;
      
      auto cmp = fastcast!(Compare) (ce.cd);
      if (!cmp) return null;
      // logln("salit "[], salit.exs, " INDEX "[], ce.cd);
      cmp = cmp.dup;
      cmp.falseOverride = salit.exs[0];
      cmp.trueOverride = salit.exs[1];
      return fastcast!(Expr) (cmp);
    }
    if (auto rt = fastcast!(RefTuple) (it)) {
      Expr[] exprs;
      bool succeeded;
      foreach (mv; rt.mvs) {
        if (auto t = subtransform(mv)) {
          succeeded = true;
          exprs ~= t;
        } else {
          exprs ~= mv;
        }
      }
      if (!succeeded) return null;
      return mkTupleExpr(exprs);
    }
    return subtransform(it);
  };
  foldopt ~= delegate Itr(Itr it) {
    auto isAnd = fastcast!(AndOp) (it), isOr = fastcast!(OrOp) (it);
    if (!isAnd && !isOr) return null;
    setupStaticBoolLits();
    Cond c1, c2;
    if (isAnd) { c1 = isAnd.c1; c2 = isAnd.c2; }
    if (isOr)  { c1 = isOr.c1;  c2 = isOr.c2;  }
    c1 = fastcast!(Cond) (fold(c1));
    c2 = fastcast!(Cond) (fold(c2));
    if (isStaticTrue(c1)) {
      if (isOr) return cTrue; // doesn't matter if cond2 is static or not
      if (isStaticTrue(c2)) return cTrue;
      else if (isStaticFalse(c2)) return cFalse;
      else return null;
    } else if (isStaticFalse(c1)) {
      if (isAnd) return cFalse; // doesn't matter if cond2 is static or not
      if (isStaticTrue(c2)) return cTrue;
      else if (isStaticFalse(c2)) return cFalse;
      else return null;
    } else return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    auto ew = fastcast!(ExprWrap) (it);
    if (!ew) return null;
    setupStaticBoolLits();
    if (isStaticTrue(ew)) return cTrue;
    if (isStaticFalse(ew)) return cFalse;
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    auto nc = fastcast!(NegCond) (it);
    if (!nc) return null;
    auto sub = fastcast!(Cond) (fold(nc.c));
    setupStaticBoolLits();
    if (isStaticTrue(sub)) return cFalse;
    if (isStaticFalse(sub)) return cTrue;
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    auto cmp = fastcast!(Compare) (it);
    if (!cmp) return null;
    auto e1 = cmp.e1;
    auto e2 = cmp.e2;
    auto i1 = fastcast!(IntExpr) (e1);
    auto i2 = fastcast!(IntExpr) (e2);
    if (auto ce1 = fastcast!(CondExpr) (e1)) {
      auto cd = fastcast!(Cond) (ce1.cd);
      if (isStaticTrue (cd)) i1 = mkInt(1);
      if (isStaticFalse(cd)) i1 = mkInt(0);
    }
    if (auto ce2 = fastcast!(CondExpr) (e2)) {
      auto cd = fastcast!(Cond) (ce2.cd);
      if (isStaticTrue (cd)) i2 = mkInt(1);
      if (isStaticFalse(cd)) i2 = mkInt(0);
    }
    // logln("e1: "[], e1, "  "[], !!i1);
    // logln("e2: "[], e2, "  "[], !!i2);
    if (!i1 || !i2) return null;
    bool result;
    if (cmp.smaller && i1.num < i2.num) result = true;
    if (cmp.equal && i1.num == i2.num) result = true;
    if (cmp.greater && i1.num > i2.num) result = true;
    Expr res;
    if (result) {
      if (cmp.trueOverride) res = cmp.trueOverride;
      else if (True) res = True;
      else return null;
    } else {
      if (cmp.falseOverride) res = cmp.falseOverride;
      else if (False) res = False;
      else return null;
    }
    return fastalloc!(ExprWrap)(res);
  };
}
