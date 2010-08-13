module ast.templ;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.fun;

class Template : Named {
  string name;
  string param;
  string source; // HAX
  Module context;
  TemplateInstance[IType] emat; // past tense of emit
  TemplateInstance getInstance(IType type, ParseCb rest) {
    if (auto p = type in emat) return *p;
    return emat[type] = new TemplateInstance(this, type, rest);
  }
  override {
    string getIdentifier() { return name; }
  }
}

Object gotTemplate(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("template")) return null;
  auto tmpl = new Template;
  if (!(t2.gotIdentifier(tmpl.name) && t2.accept("(") && t2.gotIdentifier(tmpl.param) && t2.accept(")")))
    throw new Exception("Failed parsing template header: '"~t2.next_text()~"'");
  tmpl.source = t2.getHeredoc();
  tmpl.context = namespace().get!(Module);
  text = t2;
  namespace().add(tmpl.name, tmpl);
  return Single!(NoOp);
}
mixin DefaultParser!(gotTemplate, "tree.toplevel.template");

import tools.log;

// TODO: mark matched functions as .weak
class TemplateInstance : Namespace {
  Module context;
  IType type;
  this(Template parent, IType type, ParseCb rest) {
    this.type = type;
    scope mns = new MiniNamespace(parent.name~"_mini");
    mns.add(parent.param, type);
    mns.sup = this;
    this.sup = context = parent.context;
    withTLS(namespace, mns, {
      auto t2 = parent.source;
      Tree tr;
      // logln("rest toplevel match on ", t2);
      if (!t2.many(
        !!rest(t2, "tree.toplevel", &tr),
        {
          if (cast(NoOp) tr) return;
          auto n = cast(Named) tr;
          if (!n) throw new Exception(Format("Not named: ", tr));
          if (auto fn = cast(Function) n) {// already added itself
            fn.sup = this;
            context.entries ~= fn;
          } else
            add(n.getIdentifier(), n);
        }
      ) || t2.strip().length)
        throw new Exception("Failed to parse template content at '"~t2.next_text()~"'");
        
    });
  }
  override {
    string mangle(string name, IType type) {
      return "templinst_"~type.mangle();
    }
    Stuple!(IType, string, int)[] stackframe() { assert(false); }
  }
}

Object gotTemplateInst(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string id;
  if (!t2.gotIdentifier(id) || !t2.accept("!")) return null;
  auto _t = namespace().lookup(id), t = cast(Template) _t;
  if (!_t) throw new Exception("'"~id~"' not found for template instantiation. ");
  if (!t) throw new Exception("'"~id~"' is not a template! ");
  IType ty;
  if (!rest(t2, "type", &ty)) throw new Exception("Couldn't match type for instantiation at '"~t2.next_text()~"'");
  auto inst = t.getInstance(ty, rest);
  text = t2;
  if (auto res = inst.lookup(id)) return res;
  else throw new Exception("Template '"~id~"' contains no self-named anything. ");
}
mixin DefaultParser!(gotTemplateInst, "type.templ_inst", "2");
mixin DefaultParser!(gotTemplateInst, "tree.expr.templ_expr", "45"); // I wonder if this will Just Work™
