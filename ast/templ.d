module ast.templ;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.fun;

class Template : Named {
  string name;
  string param;
  bool isAlias;
  string source; // HAX
  Namespace context;
  union {
    Stuple!(TemplateInstance, IType)[] emat_type; // past tense of emit
    Stuple!(TemplateInstance, Tree)[] emat_alias;
  }
  TemplateInstance getInstance(IType type, ParseCb rest) {
    assert(!isAlias);
    foreach (entry; emat_type)
      if (entry._1 == type) return entry._0;
    auto ti = new TemplateInstance(this, type, rest);
    emat_type ~= stuple(ti, type);
    return ti;
  }
  TemplateInstance getInstance(Tree tr, ParseCb rest) {
    assert(isAlias);
    foreach (entry; emat_alias)
      if (entry._1 == tr) return entry._0;
    auto ti = new TemplateInstance(this, tr, rest);
    emat_alias ~= stuple(ti, tr);
    return ti;
  }
  override {
    string getIdentifier() { return name; }
    string toString() { return Format("template ", name); }
  }
}

Object gotTemplate(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("template")) return null;
  auto tmpl = new Template;
  if (!(t2.gotIdentifier(tmpl.name) && t2.accept("(") && (t2.accept("alias") && test(tmpl.isAlias = true) || true) && t2.gotIdentifier(tmpl.param) && t2.accept(")")))
    throw new Exception("Failed parsing template header: '"~t2.next_text()~"'");
  tmpl.source = t2.getHeredoc();
  tmpl.context = namespace();
  text = t2;
  namespace().add(tmpl.name, tmpl);
  return Single!(NoOp);
}
// a_ so this comes first .. lol
mixin DefaultParser!(gotTemplate, "tree.toplevel.a_template");

import tools.log;

// TODO: mark matched functions as .weak
class TemplateInstance : Namespace {
  Namespace context;
  union {
    IType type;
    Tree tr;
  }
  Template parent;
  this(Template parent, IType type, ParseCb rest) {
    this.type = type;
    this.parent = parent;
    assert(!parent.isAlias);
    __add(parent.param, cast(Object) type);
    this.sup = context = parent.context;
    this(rest);
  }
  this(Template parent, Tree tr, ParseCb rest) {
    this.tr = tr;
    this.parent = parent;
    assert(parent.isAlias);
    __add(parent.param, cast(Object) tr);
    this.sup = context = parent.context;
    this(rest);
  }
  this(ParseCb rest) {
    withTLS(namespace, this, {
      auto t2 = parent.source.dup; // prevent memoizer confusion. 
      Tree tr;
      // logln("rest toplevel match on ", t2);
      if (!t2.many(
        !!rest(t2, "tree.toplevel", &tr),
        {
          if (cast(NoOp) tr) return;
          auto n = cast(Named) tr;
          // if (!n) throw new Exception(Format("Not named: ", tr));
          if (n && !addsSelf(n)) add(n.getIdentifier(), n);
          if (auto ns = cast(Namespace) tr) { // now reset sup to correct target.
            ns.sup = this;
          }
          current_module().entries ~= tr;
        }
      ) || t2.strip().length)
        throw new Exception("Failed to parse template content at '"~t2.next_text()~"'");
      
    });
  }
  override {
    string toString() { return Format("Instance of ", parent); }
    string mangle(string name, IType type) {
      string mangl;
      if (parent.isAlias) {
        if (auto fun = cast(Function) tr) {
          mangl = fun.mangleSelf();
        } else assert(false, Format(tr));
      } else mangl = this.type.mangle();
      return "templinst_"~parent.name~"_with_"~mangl
        ~"__"~sup.mangle(name, type);
    }
    Stuple!(IType, string, int)[] stackframe() { assert(false); }
    
  }
}

Object gotTemplateInst(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string id;
  if (!t2.gotIdentifier(id, true) || !t2.accept("!")) return null;
  auto _t = namespace().lookup(id), t = cast(Template) _t;
  if (!_t) return null;
  // if (!t) throw new Exception("'"~id~"' is not a template! ");
  if (!t) return null;
  TemplateInstance inst;
  if (t.isAlias) {
    Tree tr;
    if (!rest(t2, "tree.expr.named", &tr)) throw new Exception("Couldn't match tree object for instantiation at '"~t2.next_text()~"'");
    inst = t.getInstance(tr, rest);
  } else {
    IType ty;
    if (!rest(t2, "type", &ty)) throw new Exception("Couldn't match type for instantiation at '"~t2.next_text()~"'");
    inst = t.getInstance(ty, rest);
  }
  // logln("instantiate ", t.name, " with ", ty);
  text = t2;
  if (auto res = inst.lookup(t.name, true)) return res;
  else throw new Exception("Template '"~id~"' contains no self-named '"~t.name~"'. ");
}
mixin DefaultParser!(gotTemplateInst, "type.templ_inst", "2");
mixin DefaultParser!(gotTemplateInst, "tree.expr.templ_expr", "2401");

Object gotIFTI(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    Expr iter;
    auto templ = cast(Template) obj;
    if (!templ) return null;
    logln("miew ", t2.next_text());
    Expr nex;
    if (!rest(t2, "tree.expr", &nex)) return null;
    iter = iparse!(Expr, "ifti_call_test", "tree.expr")
                  (`templ!typeof(nex)(nex)`,
                   namespace(),
                   "templ", templ, "nex", nex);
    if (!iter) { logln("wat"); return null; }
    text = t2;
    return cast(Object) iter;
  };
}
mixin DefaultParser!(gotIFTI, "tree.rhs_partial.ifti");
