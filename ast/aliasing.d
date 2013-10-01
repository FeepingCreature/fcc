module ast.aliasing;

import ast.base, ast.parse, ast.structure, ast.namespace, ast.properties,
  tools.base: This, This_fn, rmSpace;

import dwarf2;

extern(C) Iterable convertLvToExpr(Iterable);
class ExprAlias : RelTransformable, Named, Expr {
  Expr base;
  string name;
  mixin MyThis!("base, name"[]);
  mixin DefaultDup!();
  mixin defaultIterate!(base);
  mixin defaultCollapse!();
  override {
    string getIdentifier() { return name; }
    Object transform(Expr relbase) {
      Statement st;
      if (auto sa = fastcast!(StatementAnd) (relbase)) {
        st = sa.first;
        relbase = sa.second;
      }
      void delegate(ref Iterable) dg;
      auto it = fastcast!(Iterable) (base);
      
      Expr finalize(Expr ex) {
        if (!st) return ex;
        return mkStatementAndExpr(st, ex);
      }
      
      bool needsTransform, needsExprConversion;
      dg = (ref Iterable iter) {
        iter.iterate(dg);
        if (auto rt = fastcast!(RelTransformable) (iter)) {
          if (fastcast!(CValue)(iter)) {
            auto thing = rt.transform(relbase);
            if (!fastcast!(CValue)(thing)) {
              // logln("needs expr conversion because ", thing, " is not a cvalue while ", iter, " was:");
              // logln("  ", it);
              needsExprConversion = true;
            }
          }
          needsTransform = true;
        }
      };
      dg(it);
      if (!needsTransform) return fastcast!(Object) (finalize(base));
      
      it = it.dup;
      if (needsExprConversion) it = convertLvToExpr(it);
      dg = (ref Iterable iter) {
        // logln("recurse[", needsExprConversion, "] ", iter);
        iter.iterate(dg);
        // logln("check[", needsExprConversion, "] ", iter);
        if (auto rt = fastcast!(RelTransformable) (iter))
          iter = fastcast!(Iterable) (rt.transform(relbase));
      };
      dg(it);
      return fastcast!(Object) (finalize(fastcast!(Expr) (it)));
    }
    void emitLLVM(LLVMFile lf) {
      fail; // Should never happen - the below foldopt should substitute them
      base.emitLLVM(lf); // may work .. or not.
    }
    IType valueType() { return base.valueType(); }
    string toString() {
      return Format("expr-alias "[], name, ""[], " = "[], base);
    }
  }
}

class CValueAlias : ExprAlias, CValue {
  mixin MyThis!("super(base, name)"[]);
  override void emitLocation(LLVMFile lf) { (fastcast!(CValue)~ base).emitLocation(lf); }
  override CValueAlias dup() { return fastalloc!(CValueAlias)(base.dup, name); }
}

final class LValueAlias : CValueAlias, LValue {
  static const isFinal = true;
  mixin MyThis!("super(base, name)"[]);
  override LValueAlias dup() { return fastalloc!(LValueAlias)(base.dup, name); }
}

final class MValueAlias : ExprAlias, MValue {
  static const isFinal = true;
  mixin MyThis!("super(base, name)"[]);
  void emitAssignment(LLVMFile lf) { (fastcast!(MValue)~ base).emitAssignment(lf); }
  override MValueAlias dup() { return fastalloc!(MValueAlias)(base.dup, name); }
}

class _TypeAlias : Named, IType, SelfAdding, Dwarf2Encodable {
  IType base;
  // strictFrom: can't implicitly cast TA to base
  // strictTo: can't implicitly cast base to TA
  bool strictFrom, strictTo;
  string name;
  override {
    bool isComplete() {
      // break circles
      if (alreadyRecursing(this)) return true;
      pushRecurse(this);
      scope(exit) popRecurse();
      return base.isComplete;
    }
    bool addsSelf() { return true; }
    string getIdentifier() { return name; }
    bool isPointerLess() { return base.isPointerLess(); }
    string llvmType() { return base.llvmType(); }
    string llvmSize() { return base.llvmSize(); }
    string mangle() {
      // breeak
      if (alreadyRecursing(this)) return qformat("recursive_alias_", name.replace("-", "_dash_"));
      pushRecurse(this); scope(exit) popRecurse();
      return qformat("type_alias_", name.replace("-", "_dash_"), "_", base.mangle);
    }
    string toString() {
      if (alreadyRecursing(this)) return qformat("recursive ", name);
      pushRecurse(this); scope(exit) popRecurse();
      string strict;
      if (strictFrom && strictTo) strict = "strict ";
      else if (strictFrom) strict = "strict(from) ";
      else if (strictTo) strict = "strict(to) ";
      return Format(strict, name, ":", base);
    }
    int opEquals(IType ty) {
      if (ty is this) return true;
      if (alreadyRecursing(this, ty)) return true; // break loop
      pushRecurse(this, ty); scope(exit) popRecurse();
      auto ta2 = fastcast!(TypeAlias) (ty);
      if (strictFrom || strictTo) {
        if (!ta2) return false;
        return name == ta2.name && base == ta2.base;
      }
      // try this first!
      if (ta2 && name == ta2.name && base == ta2.base) return true;
      // then fall back to resolved check
      return resolveType(base).opEquals(resolveType(ty));
    }
    IType proxyType() { if (strictFrom || strictTo) return null; return base; }
    bool canEncode() {
      auto d2e = fastcast!(Dwarf2Encodable)(resolveType(base));
      return d2e && d2e.canEncode();
    }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      return (fastcast!(Dwarf2Encodable) (resolveType(base))).encode(dwarf2);
    }
  }
}

final class TypeAlias : _TypeAlias {
  static const isFinal = true;
  mixin This!("base, name, strictFrom = false, strictTo = false"[]);
}

static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto ea = fastcast!(ExprAlias) (it)) {
      return fastcast!(Iterable) (ea.base.dup);
    } else return null;
  };
}

extern(C) IType resolveTup(IType, bool onlyIfChanged = false);

import ast.modules;
Object gotAlias(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string id;
  bool notDone;
  
redo:
  Expr ex;
  IType ty;
  TypeAlias ta;
  Object obj;
  
  bool strictFrom, strictTo, raw;
  if (t2.accept("strict")) {
    auto t3 = t2;
    if (t3.accept("(") && t3.accept("from") && t3.accept(")")) {
      t2 = t3;
      strictFrom = true;
    } else {
      t3 = t2;
      if (t3.accept("(") && t3.accept("to") && t3.accept(")")) {
        t2 = t3;
        strictTo = true;
      } else {
        strictFrom = strictTo = true;
      }
    }
  }
  if (t2.accept("raw"[]))    raw = true;
  
  if (!(t2.gotIdentifier(id) &&
        t2.accept("="[])))
    t2.failparse("Couldn't parse alias"[]);
  auto t3 = t2;
  bool gotTerm() {
    if (t3.accept(";"[])) return true;
    if (t3.accept(","[])) {
      notDone = true;
      return true;
    }
    return false;
  }
  
  if (rest(t3, "type"[], &ty) && gotTerm()) {
    if (auto tup = resolveTup(ty, true)) ty = tup;
    ta = fastalloc!(TypeAlias)(ty, id, strictFrom, strictTo);
    t2 = t3;
  } else {
    t3 = t2;
    string id2;
    if (t3.gotIdentifier(id2, true) && gotTerm()) {
      obj = namespace().lookup(id2);
      if (obj) t2 = t3;
    }
    if (!obj) {
      t3 = t2;
      
      auto backup = *rawmode_loc.ptr();
      if (raw) *rawmode_loc.ptr() = t3.ptr;
      scope(exit) if (raw) *rawmode_loc.ptr() = backup;
      
      if (rest(t3, "tree.expr"[], &obj) && gotTerm()) {
        t2 = t3;
      } else {
        t2.failparse("Couldn't parse alias target"[]);
      }
    }
    if (auto e = fastcast!(Expr) (obj)) { obj = null; ex = e; }
    else {
      namespace().__add(id, obj); // for instance, function alias
    }
  }
  
  assert(ex || ta || obj);
  text = t2;
  auto cv = fastcast!(CValue)~ ex, mv = fastcast!(MValue)~ ex, lv = fastcast!(LValue)~ ex;
  if (ex) {
    if (strictFrom || strictTo) t2.failparse("no such thing as strict expr-alias"[]);
    ExprAlias res;
    if (lv) res = fastalloc!(LValueAlias)(lv, id);
    else if (mv) res = fastalloc!(MValueAlias)(mv, id);
    else if (cv) res = fastalloc!(CValueAlias)(cv, id);
    else res = fastalloc!(ExprAlias)(ex, id);
    namespace().add(res);
  }
  if (ta) namespace().add(ta);
  if (notDone) {
    notDone = false;
    goto redo;
  }
  return Single!(NamedNull);
}
mixin DefaultParser!(gotAlias, "struct_member.struct_alias"[], null, "alias"[]);
mixin DefaultParser!(gotAlias, "tree.stmt.alias"[], "16"[], "alias"[]);
mixin DefaultParser!(gotAlias, "tree.toplevel.alias"[], null, "alias"[]);

import ast.casting;
static this() {
  // type alias implicitly casts to parent type (if not strictFrom)
  implicits ~= delegate Expr(Expr ex) {
    auto ta = fastcast!(TypeAlias) (ex.valueType());
    if (!ta || ta.strictFrom) return null;
    return reinterpret_cast(ta.base, ex);
  };
}
