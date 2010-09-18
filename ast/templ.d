module ast.templ;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.fun;

class Template : Named {
  string name;
  string param;
  string source; // HAX
  Module context;
  Stuple!(TemplateInstance, IType)[] emat; // past tense of emit
  TemplateInstance getInstance(IType type, ParseCb rest) {
    foreach (entry; emat)
      if (entry._1 == type) return entry._0;
    auto ti = new TemplateInstance(this, type, rest);
    emat ~= stuple(ti, type);
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
  Template parent;
  this(Template parent, IType type, ParseCb rest) {
    this.type = type;
    this.parent = parent;
    __add(parent.param, cast(Object) type);
    this.sup = context = parent.context;
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
      return "templinst_"~name~"_"~type.mangle();
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
  if (!t) throw new Exception("'"~id~"' is not a template! ");
  IType ty;
  if (!rest(t2, "type", &ty)) throw new Exception("Couldn't match type for instantiation at '"~t2.next_text()~"'");
  // logln("instantiate ", t.name, " with ", ty);
  auto inst = t.getInstance(ty, rest);
  text = t2;
  if (auto res = inst.lookup(t.name, true)) return res;
  else throw new Exception("Template '"~id~"' contains no self-named '"~t.name~"'. ");
}
mixin DefaultParser!(gotTemplateInst, "type.templ_inst", "2");
mixin DefaultParser!(gotTemplateInst, "tree.expr.templ_expr", "40");
