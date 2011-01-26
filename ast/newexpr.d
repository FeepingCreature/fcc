module ast.newexpr;

import
  ast.oop, ast.base, ast.static_arrays, ast.namespace, ast.parse,
  ast.vardecl, ast.int_literal, ast.pointer, ast.structure: doAlign;

Object gotNewClassExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  string id;
  if (!t2.gotIdentifier(id)) return null;
  auto cl = fastcast!(Class)~ namespace().lookup(id);
  if (!cl) return null;
  
  text = t2;
  return new CallbackExpr(new ClassRef(cl), cl /apply/ (Class cl, AsmFile af) {
    mixin(mustOffset("nativePtrSize"));
    mkVar(af, new ClassRef(cl), true, (Variable var) {
      mixin(mustOffset("0"));
      iparse!(Statement, "new_class", "tree.stmt")
      (`{
          var = type-of var: mem.calloc(size, 1);
          (void**:var)[0] = _classinfo;
        }`,
        "var", var,
        "size", mkInt(cl.size),
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
          "base", mkInt(base), "id", mkInt(id++),
          "_classinfo", new Symbol(cl.ci_name()),
          "offs", mkInt(offs)
        ).emitAsm(af);
      });
    });
  });
}
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class", "11", "new");

import ast.casting, ast.slice: mkPointerSlice;
Object gotNewArrayExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  
  if (auto sa = fastcast!(StaticArray)~ ty) {
    IType base = sa.elemType;
    Expr len = mkInt(sa.length);
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
    return fastcast!(Object)~
      mkPointerSlice(
        reinterpret_cast(
          new Pointer(base),
          iparse!(Expr, "do_calloc", "tree.expr")
                ("mem.calloc(len, basesz)",
                  "len", len, "basesz", mkInt(base.size))),
        mkInt(0), len);
  } else {
    Expr len;
    if (!t2.accept("[") ||
        !rest(t2, "tree.expr", &len) ||
        !gotImplicitCast(len, (IType it) { return !!cast(SysInt) it; }) ||
        !t2.accept("]"))
      return null;
    text = t2;
    // logln("new2 ", ty, " [", len, "]");
    return fastcast!(Object)~
      mkPointerSlice(
        reinterpret_cast(new Pointer(ty),
          iparse!(Expr, "new_dynamic_array", "tree.expr")
                 ("mem.calloc(len, size-of ty)", "len", len, "ty", ty)
        ),
        mkInt(0), len
      );
  }
}
mixin DefaultParser!(gotNewArrayExpr, "tree.expr.new.array", "12", "new");

Object gotNewValueExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType ty;
  if (!rest(t2, "type", &ty))
    t2.failparse("Malformed value-new");
  
  text = t2;
  
  return fastcast!(Object)~ iparse!(Expr, "new_value", "tree.expr")
    ("type*:mem.calloc(1, size-of type)",
     "type", ty
    );
}
mixin DefaultParser!(gotNewValueExpr, "tree.expr.new.value", "2", "new");

static this() { parsecon.addPrecedence("tree.expr.new", "20"); }
