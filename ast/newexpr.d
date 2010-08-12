module ast.newexpr;

import ast.oop, ast.base, ast.namespace, ast.parse, ast.vardecl, ast.int_literal, ast.pointer;

class CallbackExpr : Expr {
  IType type;
  void delegate(AsmFile) dg;
  this(IType type, void delegate(AsmFile) dg) {
    this.type = type; this.dg = dg;
  }
  override {
    IType valueType() { return type; }
    void emitAsm(AsmFile af) { dg(af); }
    mixin defaultIterate!(); // TODO
  }
}

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
          var = cast(typeof(var)) calloc(size, nps);
          (cast(void**) var)[0] = _classinfo;
        }",
        "var", var,
        "size", new IntExpr(cl.getClassinfo().length),
        "nps", new IntExpr(nativePtrSize),
        "_classinfo", new Symbol(cl.ci_name())
      ).emitAsm(af);
    });
  });
}
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class");

static this() { parsecon.addPrecedence("tree.expr.new", "25"); }
