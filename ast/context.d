module ast.context;

import ast.base, ast.parse, ast.static_arrays, ast.namespace, ast.assign, ast.globvars, ast.modules;

class Context : Namespace, MValue, Named {
  string name;
  this(string name) { this.name = name; }
  string mangleSelf() {
    return sup.mangle(name, null);
  }
  void iterValid(void delegate(Expr) dg, bool reverse = false) {
    void _body(Object entry) {
      if (auto ex = cast(Expr) entry) {
        auto lv = cast(LValue) entry, mv = cast(MValue) entry;
        if (!lv && !mv)
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
    void iterate(void delegate(ref Iterable) dg) { assert(false); }
    string mangle(string name, IType type) {
      return Format(mangleSelf(), "_", name, "_of_", type.mangle());
    }
    Stuple!(IType, string, int)[] stackframe() {
      assert(false);
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
        if (auto lv = cast(LValue) ex) {
          (new Assignment(lv, new Placeholder(lv.valueType()), false, true)).emitAsm(af);
        } else if (auto mv = cast(MValue) ex) {
          mv.emitAssignment(af);
        } else assert(false);
      });
    }
  }
}

import tools.log;
Object gotContext(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!(t2.accept("context") && t2.gotIdentifier(name))) return null;
  auto ctx = new Context(name);
  namespace().add(ctx);
  ctx.sup = namespace();
  namespace.set(ctx);
  scope(exit) namespace.set(ctx.sup);
  
  bool matchOne(ref string st) {
    Tree tr;
    if (!rest(st, "tree.toplevel", &tr)) return false;
    logln("tr is ", tr);
    namespace().get!(Module).entries ~= tr;
    if (auto gvd = cast(GlobVarDecl) tr) {
      // already added
      // foreach (var; gvd.vars)
      //   ctx.add(var);
    } else assert(!!cast(NoOp) tr);
    return true;
  }
  auto t3 = t2;
  if (t3.accept("{")) {
    t3.many(t3.matchOne());
    if (!t3.accept("}"))
      throw new Exception("Unable to parse context block at '"~t3.next_text()~"'");
    t2 = t3;
  } else t2.matchOne();
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotContext, "tree.toplevel.context");

Object gotContextMember(ref string text, ParseCb cont, ParseCb rest) {
  string t2 = text;
  assert(lhs_partial());
  auto ctx = cast(Context) lhs_partial();
  if (!ctx) return null;
  string ident;
  if (t2.accept(".") && t2.gotIdentifier(ident)) {
    auto m = ctx.lookup(ident);
    if (!m) throw new Exception("No '"~ident~"' in "~ctx.toString()~"!");
    logln("got ", m);
    text = t2;
    return m;
  } else return null;
}
mixin DefaultParser!(gotContextMember, "tree.rhs_partial.access_context_member");
