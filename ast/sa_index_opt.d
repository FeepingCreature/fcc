module ast.sa_index_opt;

import
  ast.base, ast.static_arrays, ast.math, ast.pointer,
  ast.casting, ast.int_literal;

alias ast.fold.fold fold;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto dre = fastcast!(DerefExpr) (it); if (!dre)   return null;
    if (dre.valueType() != Single!(SysInt))    return null;
    auto rce1 = fastcast!(RCE)~ dre.src; if (!rce1)  return null;
    auto pe = fastcast!(AsmIntBinopExpr) (rce1.from);
                                   if (!pe)    return null;
                                   if (pe.op != "+")
                                               return null;
    auto rce2 = fastcast!(RCE)~ fold(pe.e1); 
                                   if (!rce2)  return null;
    auto re = fastcast!(RefExpr) (rce2.from);
                                   if (!re)    return null;
    Expr data = re;
    if (auto dcmcv = fastcast!(DontCastMeCValue) (re.src))
      data = dcmcv.sup;
    auto ccast = fastcast!(RCC) (data);
                                   if (!ccast) return null;
    auto de = cast(DataExpr) ccast.from;
                                   if (!de)    return null;
    auto ioffs = fastcast!(IntExpr)~ fold(pe.e2);
                                   if (!ioffs) return null;
    auto field = cast(int[]) de.data;
    auto index = ioffs.num;
    assert(!(index & 3), "Bad index!! ");
    index /= 4;
    // yay
    return fastcast!(Iterable) (mkInt(field[index]));
  };
}
