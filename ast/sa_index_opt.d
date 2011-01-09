module ast.sa_index_opt;

import
  ast.base, ast.static_arrays, ast.math, ast.pointer,
  ast.casting, ast.int_literal;

alias ast.fold.fold fold;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    auto dre = cast(DerefExpr) it; if (!dre)   return null;
    if (dre.valueType() != Single!(SysInt))    return null;
    auto rce1 = cast(RCE) dre.src; if (!rce1)  return null;
    auto pe = cast(AsmIntBinopExpr) rce1.from;
                                   if (!pe)    return null;
                                   if (pe.op != "+")
                                               return null;
    auto rce2 = cast(RCE) fold(pe.e1); 
                                   if (!rce2)  return null;
    auto re = cast(RefExpr) rce2.from;
                                   if (!re)    return null;
    Expr data = re;
    if (auto dcmcv = cast(DontCastMeCValue) re.src)
      data = dcmcv.sup;
    auto ccast = cast(RCC) data;
                                   if (!ccast) return null;
    auto de = cast(DataExpr) ccast.from;
                                   if (!de)    return null;
    auto ioffs = cast(IntExpr) fold(pe.e2);
                                   if (!ioffs) return null;
    auto field = cast(int[]) de.data;
    auto index = ioffs.num;
    assert(!(index & 3), "Bad index!! ");
    index /= 4;
    // yay
    return mkInt(field[index]);
  };
}
