module ast.templ;

import ast.base, ast.parse, ast.modules, ast.namespace, ast.fun, ast.oop;

interface ITemplate : Named {
  Object getInstanceIdentifier(IType it, ParseCb rest, string name);
}

extern(C) bool _isITemplate(Object obj) { return !!fastcast!(ITemplate)(obj); }

interface ITemplateX : ITemplate { // extended template-like
  bool isAliasTemplate();
  TemplateInstance getInstance(IType type, ParseCb rest);
  TemplateInstance getInstance(Tree tr, ParseCb rest);
  Object postprocess(Object obj);
}

void delegate()[] resetDgs;
void resetTemplates() { foreach (dg; resetDgs) dg(); }

class RelTemplate : ITemplateX {
  Template sup;
  Expr ex;
  this(Template t, Expr e) { sup = t; ex = e; }
  override {
    bool isAliasTemplate() { return sup.isAliasTemplate(); }
    string getIdentifier() { return sup.getIdentifier(); }
    Object getInstanceIdentifier(IType it, ParseCb rest, string name) {
      return postprocess(sup.getInstanceIdentifier(it, rest, name));
    }
    TemplateInstance getInstance(IType type, ParseCb rest) {
      return sup.getInstance(type, rest);
    }
    TemplateInstance getInstance(Tree tr, ParseCb rest) {
      return sup.getInstance(tr, rest);
    }
    Object postprocess(Object obj) {
      auto rt = fastcast!(RelTransformable) (obj);
      if (!rt) return obj;
      return rt.transform(ex);
    }
  }
}

class Template : ITemplateX, SelfAdding, RelTransformable /* for templates in structs */ {
  string name;
  string param;
  bool isAlias;
  override bool isAliasTemplate() { return isAlias; }
  string source; // HAX
  Namespace context;
  union {
    Stuple!(TemplateInstance, IType)[] emat_type; // past tense of emit
    Stuple!(TemplateInstance, Tree)[] emat_alias;
  }
  this() {
    resetDgs ~= &resetme;
    context = namespace();
  }
  void resetme() { emat_type = null; emat_alias = null; }
  override {
    Object transform(Expr base) {
      return new RelTemplate(this, base);
    }
    TemplateInstance getInstance(IType type, ParseCb rest) {
      assert(!isAlias);
      TemplateInstance ti;
      foreach (entry; emat_type)
        if (entry._1 == type) { ti = entry._0; break; }
      if (!ti) {
        ti = new TemplateInstance(this, type, rest);
      }
      ti.emitCopy();
      return ti;
    }
    TemplateInstance getInstance(Tree tr, ParseCb rest) {
      assert(isAlias);
      TemplateInstance ti;
      foreach (entry; emat_alias)
        if (entry._1 == tr) { ti = entry._0; break; }
      if (!ti) {
        ti = new TemplateInstance(this, tr, rest);
      }
      ti.emitCopy();
      return ti;
    }
    Object getInstanceIdentifier(IType type, ParseCb rest, string name) {
      return getInstance(type, rest).lookup(name, true);
    }
    string getIdentifier() { return name; }
    bool addsSelf() { return true; }
    string toString() {
      return Format("template ", name);
    }
    Object postprocess(Object obj) { return obj; }
  }
}

import ast.stringparse;
Object gotTemplate(bool ReturnNoOp)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  auto tmpl = new Template;
  if (!(t2.gotIdentifier(tmpl.name) && t2.accept("(") && (t2.accept("alias") && test(tmpl.isAlias = true) || true) && t2.gotIdentifier(tmpl.param) && t2.accept(")")))
    t2.failparse("Failed parsing template header");
  t2.noMoreHeredoc();
  tmpl.source = t2.coarseLexScope(true, false);
  text = t2;
  namespace().add(tmpl.name, tmpl);
  static if (ReturnNoOp) return Single!(NoOp);
  else return tmpl;
}
// a_ so this comes first .. lol
mixin DefaultParser!(gotTemplate!(false), "tree.toplevel.a_template", null, "template");
mixin DefaultParser!(gotTemplate!(false), "struct_member.struct_template", null, "template");
mixin DefaultParser!(gotTemplate!(true), "tree.stmt.template_statement", "182", "template");

import tools.log;

class DependencyEntry : Tree {
  Dependency sup;
  this(Dependency dep) { sup = dep; }
  mixin defaultIterate!();
  DependencyEntry dup() { return this; }
  void emitAsm(AsmFile af) {
    sup.emitDependency(af);
  }
}

import ast.structure, ast.scopes, ast.literal_string;
class TemplateInstance : Namespace, HandlesEmits {
  Namespace context;
  union {
    IType type;
    Tree tr;
  }
  Template parent;
  IsMangled[] instRes;
  bool embedded; // embedded in a fun, special consideration applies for lookups
  override Object lookup(string name, bool local = false) {
    if (auto res = super.lookup(name, local)) return res;
    if (embedded && local && name != parent.name /* lol */)
      return sup.lookup(name, true); // return results from surrounding function for a nestfun
    return null;
  }
  override bool handledEmit(Tree tr) {
    // TODO: I feel VERY iffy about this.
    if (fastcast!(Module) (context)) return false;
    /*logln(tr);
    logln(" -- context ", context);
    logln();*/
    return !embedded;
  }
  this(Template parent, IType type, ParseCb rest) {
    this.type = type;
    this.parent = parent;
    assert(!parent.isAlias);
    __add(parent.param, fastcast!(Object)~ type);
    this.sup = context = parent.context;
    parent.emat_type ~= stuple(this, type);
    this(rest);
  }
  this(Template parent, Tree tr, ParseCb rest) {
    this.tr = tr;
    this.parent = parent;
    assert(parent.isAlias);
    __add(parent.param, fastcast!(Object)~ tr);
    this.sup = context = parent.context;
    parent.emat_alias ~= stuple(this, tr);
    this(rest);
  }
  Module[] ematIn;
  void emitCopy(bool weakOnly = false) {
    if (!instRes) return;
    auto mod = current_module();
    if (!mod) fail;
    // sysmod is linked into main module
    foreach (emod; ematIn) if (emod is mod || (mod.filename == mainfile && emod is sysmod)
                                           || (mod is sysmod && emod.filename == mainfile)) {
      return;
    }
    void handleDeps(Iterable outer) {
      void addDependencies(ref Iterable it) {
        it.iterate(&addDependencies);
        if (auto dep = fastcast!(Dependency) (it)) {
          mod.entries ~= new DependencyEntry(dep);
        }
      }
      addDependencies(outer);
    }
    if (weakOnly) {
      foreach (inst; instRes) if (auto fun = fastcast!(Function) (inst)) if (fun.weak) {
        mod.entries ~= fastcast!(Tree) (fun.dup);
        handleDeps(fun);
      }
    } else {
      foreach (inst; instRes) {
        mod.entries ~= fastcast!(Tree) (inst).dup; // wtf
        handleDeps(fastcast!(Iterable) (inst));
      }
    }
    ematIn ~= mod;
  }
  this(ParseCb rest) {
    withTLS(namespace, this, {
      
      auto rtptbackup = RefToParentType();
      scope(exit) RefToParentType.set(rtptbackup);
      RefToParentType.set(null);
      
      auto t2 = parent.source;
      pushCache(); // open new memoizer level
      scope(exit) popCache();
      Object obj;
      
      while (true) {
        if (auto tl = fastcast!(TemplateInstance) (context)) {
          context = tl.context;
        } else break;
      }
      
      string parsemode;
      if (fastcast!(Module) (context))
        parsemode = "tree.toplevel";
      if (fastcast!(Structure) (context))
        parsemode = "struct_member";
      if (fastcast!(Class) (context))
        parsemode = "struct_member";
      if (fastcast!(Scope) (context)) {
        parsemode = "tree.stmt.nested_fundef";
        embedded = true;
      }
      if (!parsemode) {
        logln("instance context is ", (cast(Object) context).classinfo.name);
        fail;
      }
      
      // logln("template context is ", (cast(Object) context).classinfo.name);
      // logln("rest toplevel match on ", t2);
      if (!t2.many(
        !!rest(t2, parsemode, &obj),
        {
          auto tr = fastcast!(Tree) (obj);
          if (!tr) return;
          if (fastcast!(NoOp) (obj)) return;
          auto n = fastcast!(Named)~ tr;
          // if (!n) throw new Exception(Format("Not named: ", tr));
          if (n && !addsSelf(n)) add(n.getIdentifier(), n);
          if (auto ns = fastcast!(Namespace)~ tr) { // now reset sup to correct target.
            ns.sup = this;
          }
          /*if (auto fun = fastcast!(Function)~ tr)
            logln("add ", fun.mangleSelf(), " to ", current_module().name,
              ", at ", current_module().entries.length, "; ", cast(void*) current_module());*/
          // current_module().entries ~= tr;
          auto mg = fastcast!(IsMangled) (tr);
          if (!mg) { logln("!! ", tr); fail; }
          mg.markWeak();
          // addExtra(mg);
          instRes ~= mg;
        }
      ) || t2.mystripl().length)
        t2.failparse("Failed to parse template content");
      
    });
  }
  static string[Tree] mangcache;
  override {
    string toString() {
      if (parent.isAlias) return Format("Instance of ", parent, " (", tr, ") <- ", sup);
      else return Format("Instance of ", parent, " (", type, ") <- ", sup);
    }
    string mangle(string name, IType type) {
      string mangl;
      if (parent.isAlias) {
        if (auto fun = fastcast!(Function)~ tr) {
          mangl = fun.mangleSelf();
          // logln("mangl => ", mangl);
        } else {
          if (auto ptr = tr in mangcache) mangl = *ptr;
          else {
            auto id = Format("tree_", mangcache.length);
            mangcache[tr] = id;
            mangl = id;
          }
        }
      } else mangl = this.type.mangle();
      return sup.mangle(name, type)~"__"~"templinst_"~parent.name.cleanup()~"_with_"~mangl;
    }
    Stuple!(IType, string, int)[] stackframe() {
      if (embedded) return context.stackframe();
      assert(false);
    }
  }
}

Object gotTemplateInst(bool RHSMode)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Object getInstance(Object obj) {
    auto t = fastcast!(ITemplateX) (obj);
    if (!t) return null;
    if (!t2.accept("!")) return null;
    TemplateInstance inst;
    IType ty;
    if (t.isAliasTemplate()) {
      Tree tr;
      // try plain named first
      if (!rest(t2, "tree.expr.named", &tr) && !rest(t2, "tree.expr _tree.expr.arith", &tr))
        t2.failparse("Couldn't match tree object for instantiation");
      inst = t.getInstance(tr, rest);
    } else {
      if (!rest(t2, "type", &ty))
        t2.failparse("Couldn't match type for instantiation");
      try inst = t.getInstance(ty, rest);
      catch (Exception ex) throw new Exception(Format("with ", ty, ": ", ex));
    }
    if (auto res = inst.lookup(t.getIdentifier(), true)) return t.postprocess(res);
    else throw new Exception("Template '"~t.getIdentifier()~"' contains no self-named entity! ");
  }
  static if (RHSMode) {
    return lhs_partial.using = delegate Object(Object obj) {
      try {
        auto res = getInstance(obj);
        if (res) text = t2;
        return res;
      } catch (Exception ex) {
        t2.failparse(Format("instantiating ", ex));
      }
    };
  } else {
    try {
      Object obj;
      if (!rest(t2, "tree.expr.named", &obj)) return null;
      auto res = getInstance(obj);
      if (res) text = t2;
      return res;
    } catch (Exception ex) {
      t2.failparse(Format("instantiating ", ex));
    }
  }
  // logln("instantiate ", t.name, " with ", ty);
}
mixin DefaultParser!(gotTemplateInst!(false), "type.templ_inst", "2");
mixin DefaultParser!(gotTemplateInst!(false), "tree.expr.templ_expr", "2401");
mixin DefaultParser!(gotTemplateInst!(true), "tree.rhs_partial.instance");

import ast.funcall, ast.tuples;
Object gotIFTI(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  return lhs_partial.using = delegate Object(Object obj) {
    Expr iter;
    auto templ = fastcast!(ITemplate) (obj);
    if (!templ) return null;
    Expr nex;
    if (!rest(t2, "tree.expr _tree.expr.arith", &nex)) return null;
    
    auto io = *templInstOverride.ptr(); // first level
    bool ioApplies;
    try {
      auto res = templ.getInstanceIdentifier(nex.valueType(), rest, templ.getIdentifier());
      {
        auto te = fastcast!(ITemplate) (res);
        if (io._1 && io._0.ptr == currentPropBase.ptr().ptr && te) {
          ioApplies = true;
          try {
            res = te.getInstanceIdentifier(io._1, rest, te.getIdentifier());
          } catch (Exception ex) {
            t2.failparse("ifti post-instantiating with ", io._1, ": ", ex);
          }
        }
        while (true) {
          te = fastcast!(ITemplate) (res);
          if (!te) break;
          res = te.getInstanceIdentifier(mkTuple(), rest, te.getIdentifier());
        }
      }
      auto fun = fastcast!(Function) (res);
      if (!fun) { return null; }
      text = t2;
      auto fc = buildFunCall(fun, nex, "template_call");
      if (!fc) {
        logln("Couldn't build fun call! ");
        fail;
      }
      return fastcast!(Object) (fc);
    } catch (Exception ex) {
      t2.failparse("ifti instantiating with ", nex.valueType(), ioApplies?Format(" (post ", io._1, ")"):"", ": ", ex);
    }
  };
}
mixin DefaultParser!(gotIFTI, "tree.rhs_partial.ifti");
