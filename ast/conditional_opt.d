module ast.conditional_opt;

import ast.base, ast.conditionals, ast.static_arrays, ast.fold;
import ast.int_literal, ast.math, ast.casting, ast.pointer, ast.variable, ast.assign, ast.tuples;

void setupConditionalOpt() {
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
      auto cmp = fastcast!(Compare) (ic.from);
      if (!cmp || cmp.falseOverride || cmp.trueOverride) return null;
      
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
      if (salit.exs[0].valueType().llvmType() != "i32" || salit.exs[1].valueType().llvmType != "i32")
        return null;
      
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
    return null;
    // return subtransform(it); // not safe: may replace lvalue with expr!
  };
}
