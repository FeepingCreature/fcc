module ast.context;

import ast.base, ast.parse, ast.static_arrays, ast.namespace,
  ast.assign, ast.globvars, ast.modules, ast.fun, ast.aliasing;

class Context : Namespace, MValue, Named {
  string name;
  this(string name) { this.name = name; }
  Context dup() { assert(false, "weird shit. "); }
  string toString() { return Format("context ", name, " <- ", sup); }
  string mangleSelf() {
    return sup.mangle(name, null);
  }
  void iterValid(void delegate(Expr) dg, bool reverse = false) {
    void _body(Object entry) {
      if (auto ex = fastcast!(Expr)~ entry) {
        auto lv = fastcast!(LValue)~ entry, mv = fastcast!(MValue)~ entry, ea = fastcast!(ExprAlias)~ entry;
        if (!lv && !mv && !ea)
          throw new Exception(Format("Cannot use ", ex, " in context! "));
        dg(ex);
      }
    }
    if (reverse) foreach_reverse (entry; field) _body(entry._1);
    else foreach (entry; field) _body(entry._1);
  }
  void iterValid_rev(void delegate(Expr) dg) { return iterValid(dg, true); }
  override {
    string getIdentifier() { return name; }
    void iterate(void delegate(ref Iterable) dg, IterMode mode = IterMode.Lexical) {
      if (mode == IterMode.Semantic) return;
      foreach (ref entry; field)
        if (auto it = fastcast!(Iterable) (entry._1)) {
          dg(it);
          entry._1 = fastcast!(Object) (it);
        }
    }
    string mangle(string name, IType type) {
      return Format(mangleSelf(), "_", name, "_of_", type.mangle());
    }
    Stuple!(IType, string, int)[] stackframe() {
      fail;
      return null;
    }
    void emitAsm(AsmFile af) {
      iterValid((Expr ex) { ex.emitAsm(af); });
    }
    IType valueType() {
      int size;
      iterValid((Expr ex) { size += ex.valueType().size; });
      return new StaticArray(Single!(Char), size);
    }
    void emitAssignment(AsmFile af) {
      iterValid_rev((Expr ex) {
        if (auto lv = fastcast!(LValue)~ ex) {
          (new Assignment(lv, new Placeholder(lv.valueType()), false, true)).emitAsm(af);
        } else if (auto mv = fastcast!(MValue)~ ex) {
          mv.emitAssignment(af);
        } else fail;
      });
    }
  }
}

import tools.log;
Object gotContext(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!t2.gotIdentifier(name)) return null;
  auto ctx = new Context(name);
  namespace().add(ctx);
  // logln("got context ", name, ", sup is ", namespace());
  ctx.sup = namespace();
  namespace.set(ctx);
  scope(exit) namespace.set(ctx.sup);
  
  bool matchOne(ref string st) {
    Object obj;
    if (!rest(st, "tree.toplevel", &obj)) return false;
    // namespace().get!(Module).entries ~= tr;
    if (auto tr = fastcast!(Tree) (obj))
      fastcast!(Module) (current_module()).entries ~= tr;
    if (fastcast!(GlobVarDecl) (obj) || fastcast!(Function) (obj)) {
    } else if (!fastcast!(NoOp) (obj)) {
      logln("! ", obj);
      fail;
    }
    return true;
  }
  auto t3 = t2;
  if (t3.accept("{")) {
    t3.many(t3.matchOne());
    if (!t3.accept("}"))
      t3.failparse("Unable to parse context block");
    t2 = t3;
  } else t2.matchOne();
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotContext, "tree.toplevel.context", null, "context");

Object gotContextMember(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  assert(lhs_partial());
  auto ctx = cast(Context) lhs_partial();
  if (!ctx) return null;
  string ident;
  if (t2.gotIdentifier(ident)) {
    retry:
    auto m = ctx.lookup(ident);
    if (!m)
      if (t2.eatDash(ident)) goto retry;
      else return null;
    // if (!m) throw new Exception("No '"~ident~"' in "~ctx.toString()~"!");
    text = t2;
    return m;
  } else return null;
}
mixin DefaultParser!(gotContextMember, "tree.rhs_partial.access_context_member", null, ".");
