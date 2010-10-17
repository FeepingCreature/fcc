module ast.structfuns;

import ast.fun, ast.nestfun, ast.base, ast.structure, ast.variable,
  ast.pointer, ast.dg, ast.namespace, tools.base: This, This_fn, rmSpace;

import ast.modules;
Object gotStructFunDef(ref string text, ParseCb cont, ParseCb rest) {
  auto rs = cast(RelNamespace) namespace();
  if (!rs)
    throw new Exception(Format("Fail: namespace is ", namespace(), ". "));
  auto fun = new RelFunction(rs);
  
  if (auto res = gotGenericFunDef(fun, cast(Namespace) null, true, text, cont, rest)) {
    current_module().entries ~= cast(Tree) res;
    return res;
  } else return null;
}
mixin DefaultParser!(gotStructFunDef, "struct_member.struct_fundef");

import ast.parse, tools.log;
Object gotStructFun(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  return lhs_partial.using = delegate Object(Expr ex) {
    ex = depointer(ex);
    auto strtype = cast(Structure) ex.valueType();
    if (!strtype) return null;
    string member;
    if (t2.accept(".") && t2.gotIdentifier(member)) {
      auto mvar = strtype.lookup(member);
      if (!mvar) return null;
      auto smf = cast(RelFunction) mvar;
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
  override RelFunCall dup() {
    auto res = new RelFunCall(baseptr.dup);
    res.fun = fun;
    res.params = params.dup;
    foreach (ref entry; params) entry = entry.dup;
    return res;
  }
  override void emitAsm(AsmFile af) {
    if (auto lv = cast(LValue) baseptr) {
      callDg(af, fun.type.ret, params,
        new DgConstructExpr(fun.getPointer(), new RefExpr(lv)));
    } else {
      mkVar(af, valueType(), true, (Variable var) {
        auto backup = af.checkptStack();
        scope(exit) af.restoreCheckptStack(backup);
        auto temp = new Variable(baseptr.valueType(), null, boffs(baseptr.valueType(), af.currentStackDepth));
        {
          auto vd = new VarDecl;
          vd.vars ~= temp;
          vd.emitAsm(af);
        }
        (new Assignment(temp, baseptr)).emitAsm(af);
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
    basetype = cast(IType) rn;
    assert(!!basetype);
  }
  RelFunction alloc() { return new RelFunction; }
  RelFunction dup() {
    auto res = cast(RelFunction) super.dup();
    res.context = context;
    res.baseptr = baseptr;
    res.basetype = basetype;
    return res;
  }
  override Object transform(Expr base) {
    assert(!baseptr, Format("RelFun was pretransformed: ", baseptr));
    assert(!!cast(RelNamespace) basetype);
    auto res = dup();
    res.baseptr = base;
    return res;
  }
  FunctionPointer typeAsFp() {
    auto res = new FunctionPointer;
    res.ret = type.ret;
    foreach (param; type.params)
      res.args ~= param._0;
    if (auto rnfb = cast(RelNamespaceFixupBase) context)
      res.args ~= rnfb.genCtxType(context);
    else
      res.args ~= new Pointer(basetype);
    return res;
  }
  mixin defaultIterate!(baseptr);
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
    int fixup() {
      auto cur = super.fixup();
      if (!cast(hasRefType) context)
        logln("bad context: ", context, " is not reftype");
      add(new Variable((cast(hasRefType) context).getRefType(), "__base_ptr", cur));
      return cur + 4;
    }
    Object lookup(string name, bool local = false) {
      auto res = super.lookup(name, true);
      if (res) return res;
      else if (local) return null;
      
      auto bp = cast(Expr) lookup("__base_ptr", true);
      if (auto ptr = cast(Pointer) bp.valueType()) bp = new DerefExpr(bp);
      if (auto res = context.lookupRel(name, bp))
        return res;
      
      return null;
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
    super(fun.getPointer(), new RefExpr(cast(CValue) fun.baseptr));
  }
  override typeof(this) dup() { return new typeof(this)(fun); }
  override string toString() {
    return Format("&", fun.baseptr, ".", fun);
  }
  override IType valueType() {
    return new Delegate(fun.type.ret, fun.type.params /map/ ex!("a, b -> a"));
  }
}

Object gotStructfunRefExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("&")) return null;
  
  string ident;
  RelFunction rf;
  if (!rest(t2, "tree.expr _tree.expr.arith", &rf)) return null;
  
  text = t2;
  return new StructFunRefExpr(rf);
}
mixin DefaultParser!(gotStructfunRefExpr, "tree.expr.dg_struct_ref", "21015");
