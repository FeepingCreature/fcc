module ast.structfuns;

import ast.fun, ast.nestfun, ast.base, ast.structure, ast.variable,
  ast.pointer, ast.dg, ast.namespace, tools.base: This, This_fn, rmSpace;

import ast.modules;
Object gotStructFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto rs = fastcast!(RelNamespace)~ namespace();
  if (!rs)
    throw new Exception(Format("Fail: namespace is ", namespace(), ". "));
  auto fun = new RelFunction(rs);
  
  if (auto res = gotGenericFunDef(fun, cast(Namespace) null, true, text, cont, rest)) {
    current_module().entries ~= fastcast!(Tree)~ res;
    return res;
  } else return null;
}
mixin DefaultParser!(gotStructFunDef, "struct_member.struct_fundef");

import ast.parse, tools.log;
Object gotStructFun(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  return lhs_partial.using = delegate Object(Expr ex) {
    ex = depointer(ex);
    auto strtype = fastcast!(Structure)~ ex.valueType();
    if (!strtype) return null;
    string member;
    if (t2.accept(".") && t2.gotIdentifier(member)) {
      retry:
      auto mvar = strtype.lookup(member);
      if (!mvar)
        if (t2.eatDash(member)) goto retry;
        else return null;
      auto smf = fastcast!(RelFunction) (mvar);
      if (!smf) return null;
      text = t2;
      return smf.transform(ex);
    } else return null;
  };
}
mixin DefaultParser!(gotStructFun, "tree.rhs_partial.structfun");

import ast.vardecl, ast.assign;
class RelFunCall : FunCall {
  Expr baseptr;
  this(Expr ex) {
    baseptr = ex;
  }
  mixin defaultIterate!(baseptr, params);
  override RelFunCall dup() {
    auto res = new RelFunCall(baseptr.dup);
    res.fun = fun;
    res.params = params.dup;
    foreach (ref entry; params) entry = entry.dup;
    return res;
  }
  override void emitAsm(AsmFile af) {
    if (auto lv = fastcast!(LValue)~ baseptr) {
      callDg(af, fun.type.ret, params,
        new DgConstructExpr(fun.getPointer(), new RefExpr(lv)));
    } else {
      mkVar(af, valueType(), true, (Variable var) {
        auto backup = af.checkptStack();
        scope(exit) af.restoreCheckptStack(backup);
        auto temp = new Variable(baseptr.valueType(), null, baseptr, boffs(baseptr.valueType(), af.currentStackDepth));
        {
          auto vd = new VarDecl;
          vd.vars ~= temp;
          vd.emitAsm(af);
        }
        auto res = new Variable(valueType(), null, boffs(valueType(), af.currentStackDepth));
        callDg(af, fun.type.ret, params,
          new DgConstructExpr(fun.getPointer(), new RefExpr(temp)));
        (new Assignment(var, res)).emitAsm(af);
      });
    }
  }
  override IType valueType() {
    return fun.type.ret;
  }
}

class RelFunction : Function, RelTransformable {
  Expr baseptr; // unique per instance
  IType basetype; // for mangling purposes
  RelNamespace context;
  private this() { }
  this(RelNamespace rn) {
    context = rn;
    basetype = fastcast!(IType)~ rn;
    assert(!!basetype);
  }
  RelFunction alloc() { return new RelFunction; }
  RelFunction dup() {
    auto res = fastcast!(RelFunction) (super.dup());
    res.context = context;
    res.baseptr = baseptr;
    res.basetype = basetype;
    return res;
  }
  override Object transform(Expr base) {
    assert(!baseptr, Format("RelFun was pretransformed: ", baseptr));
    assert(!!fastcast!(RelNamespace) (basetype));
    auto res = dup();
    res.baseptr = base;
    return res;
  }
  FunctionPointer typeAsFp() {
    auto res = new FunctionPointer;
    res.ret = type.ret;
    res.args = type.params.dup;
    if (auto rnfb = fastcast!(RelNamespaceFixupBase) (context))
      res.args ~= Argument(rnfb.genCtxType(context));
    else
      res.args ~= Argument(new Pointer(basetype));
    return res;
  }
  mixin defaultIterate!(baseptr, tree);
  override {
    string mangleSelf() {
      return basetype.mangle() ~ "_" ~ super.mangleSelf();
    }
    string mangle(string name, IType type) {
      return mangleSelf() ~ "_" ~ type.mangle()~"_"~name;
    }
    FunCall mkCall() {
      auto res = new RelFunCall(baseptr);
      res.fun = this;
      return res;
    }
    import ast.aliasing;
    int fixup() {
      auto cur = super.fixup();
      if (!fastcast!(hasRefType) (context))
        logln("bad context: ", context, " is not reftype");
      auto bp = new Variable((fastcast!(hasRefType) (context)).getRefType(), "__base_ptr", cur);
      add(bp); cur += 4;
      if (fastcast!(Pointer)~ bp.valueType())
        add(new ExprAlias(new DerefExpr(bp), "this"));
      return cur;
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, true);
      if (res) return res;
      else if (local) return null;
      
      auto bp = fastcast!(Expr) (lookup("__base_ptr", true));
      if (bp) { // initialized already?
        if (auto ptr = fastcast!(Pointer)~ bp.valueType()) bp = new DerefExpr(bp);
        if (auto res = context.lookupRel(name, bp))
          return res;
      }
      
      return super.lookup(name, false);
    }
  }
}

// &foo.fun, stolen from ast.nestfun
class StructFunRefExpr : mkDelegate {
  RelFunction fun;
  this(RelFunction fun) {
    this.fun = fun;
    logln("base ptr is ", fun.baseptr);
    assert(fun.baseptr);
    super(fun.getPointer(), new RefExpr(fastcast!(CValue)~ fun.baseptr));
  }
  override typeof(this) dup() { return new typeof(this)(fun); }
  override string toString() {
    return Format("&", fun.baseptr, ".", fun);
  }
  override IType valueType() {
    return new Delegate(fun.type.ret, fun.type.params);
  }
}

Object gotStructfunRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  string ident;
  RelFunction rf;
  if (!rest(text, "tree.expr _tree.expr.arith "
  ~">tree.expr.properties.tup_call >tree.expr.properties.no_tup_call", &rf))
    return null;
  
  return new StructFunRefExpr(rf);
}
mixin DefaultParser!(gotStructfunRefExpr, "tree.expr.dg_struct_ref", "21010", "&");
