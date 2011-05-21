module ast.conditional_opt;

import ast.base, ast.conditionals, ast.index, ast.static_arrays;

static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto ew = fastcast!(ExprWrap) (it);
    if (!ew) return null;
    auto ce = fastcast!(CondExpr) (ew.ex);
    if (!ce) return null;
    return ce.cd;
  };
  foldopt ~= delegate Itr(Itr it) {
    auto sie = fastcast!(SAIndexExpr) (it);
    if (!sie) return null;
    auto salit = fastcast!(SALiteralExpr) (sie.ex);
    if (!salit || salit.exs.length != 2) return null;
    if (salit.exs[0].valueType().size != 4 || salit.exs[1].valueType().size != 4)
      return null;
    auto ce = fastcast!(CondExpr) (sie.pos);
    if (!ce) return null;
    auto cmp = cast(Compare) ce.cd;
    if (!cmp) return null;
    // logln("salit ", salit.exs, " INDEX ", ce.cd);
    cmp = cmp.dup;
    cmp.falseOverride = salit.exs[0];
    cmp.trueOverride = salit.exs[1];
    return fastcast!(Itr) (cmp);
  };
}
