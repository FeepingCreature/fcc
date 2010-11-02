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
          var = typeof(var): mem.calloc(size, 1);
          (void**:var)[0] = _classinfo;
        }`,
        "var", var,
        "size", new IntExpr(cl.size),
        "_classinfo", new Symbol(cl.ci_name())
      ).emitAsm(af);
      auto base = cl.mainSize();
      doAlign(base, voidp);
      base /= 4;
      int id = 0;
      void iterLeaves(void delegate(Intf, int) dg) {
        void recurse(Intf intf, int myOffs) {
          if (intf.parents.length) foreach (i, intf2; intf.parents) {
            recurse(intf2, myOffs);
            myOffs += intf2.clsize();
          }
          else dg(intf, myOffs);
        }
        auto offs = cl.ownClassinfoLength;
        foreach (i, intf; cl.iparents) {
          recurse(intf, offs);
          offs += intf.clsize();
        }
      }
      iterLeaves((Intf intf, int offs) {
        logln("init [", base, " + ", id, "] with intf ", intf.name, "; offs ", offs);
        iparse!(Statement, "init_intfs", "tree.semicol_stmt.assign")
        (`(void**:var)[base + id] = (void**:_classinfo + offs)`,
          "var", var,
          "base", new IntExpr(base), "id", new IntExpr(id++),
          "_classinfo", new Symbol(cl.ci_name()),
          "offs", new IntExpr(offs)
        ).emitAsm(af);
      });
    });
  });
}
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class", "11");

import ast.casting, ast.slice: mkPointerSlice;
Object gotNewArrayExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("new")) return null;
  
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  
  if (auto sa = cast(StaticArray) ty) {
    IType base = sa.elemType;
    Expr len = new IntExpr(sa.length);
    auto t3 = t2;
    Expr newlen;
    if (t3.accept("[") &&
        rest(t3, "tree.expr", &newlen) &&
        gotImplicitCast(newlen, (IType it) { return !!cast(SysInt) it; }) &&
        t3.accept("]")) {
      t2 = t3;
      len = newlen;
      base = sa;
    }
    text = t2;
    // logln("new1 ", base, " [", len, "]");
    return cast(Object)
      mkPointerSlice(
        reinterpret_cast(
          new Pointer(base),
          iparse!(Expr, "do_calloc", "tree.expr")
                ("mem.calloc(len, basesz)",
                  "len", len, "basesz", new IntExpr(base.size))),
        new IntExpr(0), len);
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
             ("(ty*:mem.calloc(len, ty.sizeof))[0 .. len]",
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
    ("type*:mem.calloc(1, type.sizeof)",
     "type", ty
    );
}
mixin DefaultParser!(gotNewValueExpr, "tree.expr.new.value", "2");

static this() { parsecon.addPrecedence("tree.expr.new", "20"); }
