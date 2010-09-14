module ast.newexpr;

import
  ast.oop, ast.base, ast.static_arrays, ast.namespace, ast.parse,
  ast.vardecl, ast.int_literal, ast.pointer, ast.structure: doAlign;

Object gotNewClassExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("new")) return null;
  
  string id;
  if (!t2.gotIdentifier(id)) return null;
  auto cl = cast(Class) namespace().lookup(id);
  if (!cl) return null;
  
  text = t2;
  return new CallbackExpr(new ClassRef(cl), cl /apply/ (Class cl, AsmFile af) {
    mixin(mustOffset("nativePtrSize"));
    mkVar(af, new ClassRef(cl), true, (Variable var) {
      mixin(mustOffset("0"));
      iparse!(Statement, "new_class", "tree.stmt")
      (`{
          var = cast(typeof(var)) mem.calloc(size, nps);
          (cast(void**) var)[0] = _classinfo;
        }`,
        "var", var,
        "size", new IntExpr(cl.getClassinfo().length),
        "nps", new IntExpr(nativePtrSize),
        "_classinfo", new Symbol(cl.ci_name())
      ).emitAsm(af);
      auto offs = cl.ownClassinfoLength, base = cl.mainSize();
      doAlign(base, voidp);
      base /= 4;
      int id = 0;
      cl.getIntfLeaves((Intf intf) {
        iparse!(Statement, "init_intfs", "tree.semicol_stmt.assign")
        (`(cast(void**) var)[base + id] = cast(void*) ((cast(void**) _classinfo) + offs)`,
          "var", var,
          "base", new IntExpr(base), "id", new IntExpr(id++),
          "_classinfo", new Symbol(cl.ci_name()),
          "offs", new IntExpr(offs)
        ).emitAsm(af);
        offs += intf.clsize();
      });
    });
  });
}
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class", "11");

import ast.casting;
Object gotNewArrayExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("new")) return null;
  
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  
  if (auto sa = cast(StaticArray) ty) {
    auto base = sa.elemType, len = new IntExpr(sa.length);
    text = t2;
    // logln("new1 ", base, " [", len, "]");
    return cast(Object)
      iparse!(Expr, "new_static_array", "tree.expr")
             ("((cast(base*) mem.calloc(len, base.sizeof)))[0 .. len]",
              "len", len, "base", base
             );
  } else {
    Expr len;
    if (!t2.accept("[") ||
        !rest(t2, "tree.expr", &len) ||
        !gotImplicitCast(len, (IType it) { return !!cast(SysInt) it; }) ||
        !t2.accept("]"))
      return null;
    text = t2;
    // logln("new2 ", ty, " [", len, "]");
    return cast(Object)
      iparse!(Expr, "new_dynamic_array", "tree.expr")
             ("(cast(ty*) mem.calloc(len, ty.sizeof))[0 .. len]",
              "len", len, "ty", ty
             );
  }
}
mixin DefaultParser!(gotNewArrayExpr, "tree.expr.new.array", "12");

Object gotNewValueExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("new")) return null;
  
  IType ty;
  if (!rest(t2, "type", &ty))
    throw new Exception("Malformed value-new at '"~t2.next_text()~"'");
  
  text = t2;
  
  return cast(Object) iparse!(Expr, "new_array", "tree.expr")
    ("cast(type*) mem.calloc(1, type.sizeof)",
     "type", ty
    );
}
mixin DefaultParser!(gotNewValueExpr, "tree.expr.new.value", "2");

static this() { parsecon.addPrecedence("tree.expr.new", "25"); }
