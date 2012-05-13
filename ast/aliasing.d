module ast.aliasing;

import ast.base, ast.parse, ast.structure, ast.namespace, ast.properties,
  tools.base: This, This_fn, rmSpace;

import dwarf2;

class ExprAlias : RelTransformable, Named, Expr {
  Expr base;
  string name;
  mixin MyThis!("base, name"[]);
  mixin DefaultDup!();
  mixin defaultIterate!(base);
  override {
    string getIdentifier() { return name; }
    Object transform(Expr relbase) {
      void delegate(ref Iterable) dg;
      auto it = fastcast!(Iterable) (base);
      
      bool needsTransform;
      dg = (ref Iterable iter) {
        iter.iterate(dg);
        if (auto rt = fastcast!(RelTransformable) (iter))
          needsTransform = true;
      };
      dg(it);
      if (!needsTransform) return fastcast!(Object) (base);
      
      it = it.dup;
      dg = (ref Iterable iter) {
        iter.iterate(dg);
        if (auto rt = fastcast!(RelTransformable) (iter))
          iter = fastcast!(Iterable) (rt.transform(relbase));
      };
      dg(it);
      return fastcast!(Object) (it);
    }
    void emitAsm(AsmFile af) {
      fail; // Should never happen - the below foldopt should substitute them
      base.emitAsm(af); // may work .. or not.
    }
    IType valueType() { return base.valueType(); }
    string toString() {
      return Format("expr-alias "[], name, ""[], " = "[], base);
    }
  }
}

class CValueAlias : ExprAlias, CValue {
  mixin MyThis!("super(base, name)"[]);
  override void emitLocation(AsmFile af) { (fastcast!(CValue)~ base).emitLocation(af); }
  override CValueAlias dup() { return fastalloc!(CValueAlias)(base.dup, name); }
}

class LValueAlias : CValueAlias, LValue {
  mixin MyThis!("super(base, name)"[]);
  override LValueAlias dup() { return fastalloc!(LValueAlias)(base.dup, name); }
}

class MValueAlias : ExprAlias, MValue {
  mixin MyThis!("super(base, name)"[]);
  override void emitAssignment(AsmFile af) { (fastcast!(MValue)~ base).emitAssignment(af); }
  override MValueAlias dup() { return fastalloc!(MValueAlias)(base.dup, name); }
}

class TypeAlias : Named, IType, SelfAdding, Dwarf2Encodable {
  IType base;
  bool strict;
  string name;
  mixin This!("base, name, strict = false"[]);
  override {
    bool isComplete() { return base.isComplete; }
    bool addsSelf() { return true; }
    string getIdentifier() { return name; }
    bool isPointerLess() { return base.isPointerLess(); }
    int size() { return base.size; }
    string mangle() { return "type_alias_"~name.replace("-"[], "_dash_"[])~"_"~base.mangle; }
    ubyte[] initval() { return base.initval; }
    int opEquals(IType ty) {
      if (strict) {
        auto ta2 = fastcast!(TypeAlias) (ty);
        if (!ta2) return false;
        return base == ta2.base && name == ta2.name;
      }
      return base.opEquals(resolveType(ty));
    }
    IType proxyType() { if (strict) return null; return base; }
    string toString() { return Format(name, ":"[], base); }
    bool canEncode() {
      auto d2e = fastcast!(Dwarf2Encodable)(resolveType(base));
      return d2e && d2e.canEncode();
    }
    Dwarf2Section encode(Dwarf2Controller dwarf2) {
      return (fastcast!(Dwarf2Encodable) (resolveType(base))).encode(dwarf2);
    }
  }
}

static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto ea = fastcast!(ExprAlias) (it)) {
      return fastcast!(Iterable) (ea.base);
    } else return null;
  };
}

import ast.modules;
Object gotAlias(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string id;
  bool notDone;
  
redo:
  Expr ex;
  IType ty;
  Object obj;
  
  bool strict, raw;
  if (t2.accept("strict"[])) strict = true;
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
    t2 = t3;
  } else {
    ty = null;
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
    else namespace().__add(id, obj); // for instance, function alias
  }
  
  assert(ex || ty || obj);
  text = t2;
  auto cv = fastcast!(CValue)~ ex, mv = fastcast!(MValue)~ ex, lv = fastcast!(LValue)~ ex;
  if (ex) {
    if (strict) t2.failparse("no such thing as strict expr-alias"[]);
    ExprAlias res;
    if (lv) res = fastalloc!(LValueAlias)(lv, id);
    else if (mv) res = fastalloc!(MValueAlias)(mv, id);
    else if (cv) res = fastalloc!(CValueAlias)(cv, id);
    else res = fastalloc!(ExprAlias)(ex, id);
    namespace().add(res);
  }
  if (ty) namespace().add(fastalloc!(TypeAlias)(ty, id, strict));
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
  // type alias implicitly casts to parent type
  implicits ~= delegate Expr(Expr ex) {
    auto ta = fastcast!(TypeAlias) (ex.valueType());
    if (!ta || !ta.strict) return null;
    return reinterpret_cast(ta.base, ex);
  };
}
