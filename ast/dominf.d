// dominant supertype inference
module ast.dominf;

import ast.base, ast.types, ast.tuples, ast.casting, ast.typeset;
import tools.functional;

/**
 * currently used for return type inference
 * NOTE: must only be used if no further semantics depend on the
 * exact type of the expression being unified, until emit phase.
 * What it does:
  * for some set S_1 .. S_n of source types
  * SupType(S_x, S) = ∀ S_n in S: implicitly_converts(S_n, S_x).
  * Find the S_x so that SupType(S_x, S) ∧ ∀ S_y: SupType(S_y, s) -> implicitly_converts(S_x, S_y)
 * in other words, find the maximally specific common supertype for a set of types
  * where "supertype" is used in the more general sense of
  * "a type that we implicitly cast to"
 **/
class InferredSupertype : IType {
  Expr*[] baseExprs;
  IType currentCombinedType;
  this(Expr* exp) { addValue(exp); }
  void addValue(Expr* exp) {
    const deb = false; // debug mode
    auto ex = *exp;
    if (baseExprs.length) {
      assert(currentCombinedType);
      // easiest case: new expr matches existing type.
      // note: new exprs can never _expand_ our merge set, only reduce it
      // so we don't need to rebuild the currentCombinedType in this case
      if (gotImplicitCast(ex, currentCombinedType, (IType it2) {
        return test(it2 == currentCombinedType);
      }))
      {
        *exp = ex;
        baseExprs ~= exp;
        return;
      }
      
      auto newExprs = new Expr[baseExprs.length];
      // build the result set of supertypes:
      // enumerate all implcasts for the new expression
      // see if they're also reachable from all existing types
      // if yes, add them to the result set
      IType[] fittingTypes;
      auto _ex = ex;
      gotImplicitCast(_ex, (IType it) {
        bool oneFailed;
        foreach (i, exp2; baseExprs) {
          auto ex2 = *exp2;
          if (!gotImplicitCast(ex2, it, (IType it2) {
            return test(it2 == it);
          }))
          {
            if (deb) logln("fail ", it, " because ", ex2.valueType());
            oneFailed = true;
            break;
          }
          newExprs[i] = ex2;
        }
        if (!oneFailed) {
          if (deb) logln("add ", it, " to set");
          fittingTypes ~= it;
        } else {
          if (deb) logln("skip ", it, ": at least one failed");
        }
        return false;
      });
      if (!fittingTypes.length) {
        logln("Failed to merge ", ex.valueType(), " with ", baseExprs /map/ (Expr ex) { return ex.valueType(); });
        fail; // todo t2.failparse
      }
      
      // does src always implcast to target
      bool dominates(IType src, IType target) {
        if (src == target) return true; // heh
        Expr srcex = fastalloc!(PlaceholderToken)(src, "dominance test");
        // has to make it WITHOUT prompting!! we won't have prompting at the return site
        return !!gotImplicitCast(srcex, /*target,*/ (IType it) { return test(it == target); });
      }
      // remove types that are implcastable to or from a type already in the set
      // ie. only include "roots"
      IType[] reducedFittingTypes;
      outer:foreach (ft; fittingTypes) {
        foreach (i, ref rft; reducedFittingTypes) {
          if (dominates(ft, rft)) { // replace it in the result set
            if (deb) logln(ft, " dominates ", rft, ", replacing");
            rft = ft;
            continue outer;
          }
          if (dominates(rft, ft)) { // no need to include this type
            if (deb) logln(rft, " dominates ", ft, ", skipping");
            continue outer;
          }
        }
        reducedFittingTypes ~= ft;
      }
      
      if (reducedFittingTypes.length == 1)
        currentCombinedType = reducedFittingTypes[0];
      else
        currentCombinedType = fastalloc!(Typeset)(mkTuple(reducedFittingTypes));
      
      baseExprs ~= exp;
      foreach (i, exp2; baseExprs) {
        auto ex2 = *exp2;
        if (!gotImplicitCast(ex2, currentCombinedType, (IType it2) {
          return test(it2 == currentCombinedType);
        })) fail; // should never happen
        *exp2 = ex2;
      }
    } else {
      currentCombinedType = ex.valueType();
      baseExprs ~= exp;
    }
  }
  override {
    string toString() { return qformat("(merged) ", currentCombinedType); }
    // replace with current type at end of function
    string llvmType() { assert(false); }
    string llvmSize() { assert(false); }
    string mangle() { assert(false); }
    bool opEquals(IType it2) { assert(false); }
    IType proxyType() {
      if (!currentCombinedType) {
        logln("Cannot generate proxy type: no types in supertype set");
      }
      return currentCombinedType;
    }
    bool isPointerLess() { assert(false); /* what??! */ }
    bool isComplete() { return false; } // certainly not!!
  }
}

IType finalizeMergeType(IType it) {
  if (auto ist = fastcast!(InferredSupertype)(it))
    return ist.currentCombinedType;
  return it;
}
