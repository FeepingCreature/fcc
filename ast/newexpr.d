module ast.newexpr;

import ast.oop, ast.base, ast.namespace, ast.parse, ast.vardecl, ast.int_literal, ast.pointer, ast.structure: doAlign;

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
      ("{
          var = cast(typeof(var)) mem.calloc(size, nps);
          (cast(void**) var)[0] = _classinfo;
        }",
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
        (`(cast(void**) var)[base + id] = (cast(void**) _classinfo) + offs`,
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
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class");

Object gotNewArrayExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("new")) return null;
  
  IType ty;
  Expr sz;
  if (!t2.accept("(")) return null;
  if (!rest(t2, "tree.expr", &sz, (Expr ex) {
    return !!cast(SysInt) ex.valueType();
  }))
    throw new Exception("Fail to parse new() size expression at '"~t2.next_text()~"'");
  if (!t2.accept(")") || !rest(t2, "type", &ty))
    throw new Exception("Malformed array-new at '"~t2.next_text()~"'");
  
  text = t2;
  
  return cast(Object) iparse!(Expr, "new_array", "tree.expr")
    ("(cast(type*) mem.calloc(len, type.sizeof))[0 .. len]",
     "type", ty,
     "len", sz
    );
}
mixin DefaultParser!(gotNewArrayExpr, "tree.expr.new.array");

static this() { parsecon.addPrecedence("tree.expr.new", "25"); }
