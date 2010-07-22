module ast.structure;

import ast.types, ast.base, ast.namespace, parseBase;

import tools.base: ex;
int sum(S, T)(S s, T t) {
  int res;
  foreach (entry; s)
    res += t(entry);
  return res;
}

// next power of two
int np2(int i) {
  int p = 1;
  while (p < i) p *= 2;
  return p;
}

int roundTo(int i, int to) {
  auto i2 = (i / to) * to;
  if (i2 != i) return i2 + to;
  else return i;
}

void doAlign(ref int offset, IType type) {
  offset = roundTo(offset, np2(type.size()));
}

import tools.log;
class RelMember : Expr, Named, RelTransformable {
  string name;
  IType type;
  int offset;
  override {
    string toString() { return Format("[", name, ": ", type, " @", offset, "]"); }
    IType valueType() { return type; }
    void emitAsm(AsmFile af) {
      assert(false, "Rel member untransformed: cannot emit. ");
    }
    mixin defaultIterate!();
    string getIdentifier() { return name; }
    Object transform(Expr base) {
      return cast(Object) mkMemberAccess(base, name);
    }
  }
  this(string name, IType type, Namespace ns) {
    this.name = name;
    this.type = type;
    offset = (cast(IType) ns).size();
    // alignment
    doAlign(offset, type);
    ns.add(this);
  }
}

class Structure : Namespace, RelNamespace, IType, Named {
  mixin TypeDefaults!();
  string name;
  int size() {
    int res;
    select((string, RelMember member) {
      auto end = member.offset + member.type.size;
      if (end > res) res = end;
    });
    return res;
  }
  this(string name) {
    this.name = name;
  }
  string mangle() { return "struct_"~name; }
  override {
    string getIdentifier() { return name; }
    string mangle(string name, IType type) { return "struct_"~name~"_"~type.mangle()~"_"~name; }
    Stuple!(IType, string, int)[] stackframe() {
      Stuple!(IType, string, int)[] res;
      select((string, RelMember member) { res ~= stuple(member.type, member.name, member.offset); });
      return res;
    }
    Object lookupRel(string str, Expr base) {
      auto res = super.lookup(str);
      if (auto rt = cast(RelTransformable) res)
        return cast(Object) rt.transform(base);
      return res;
    }
    string toString() {
      auto res = super.toString() ~ " { ";
      select((string, RelMember member) { res ~= Format(member.name, ": ", member.type, "; "); });
      return res ~ " }";
    }
  }
}

bool matchStructBody(ref string text, Namespace ns,
                     ParseCb cont, ParseCb rest) {
  auto backup = namespace();
  namespace.set(ns);
  scope(exit) namespace.set(backup);
  
  Named smem;
  string t2;
  string[] names; IType[] types;
  string strname; IType strtype;
  return (
    text.many(
      (t2 = text, true)
      && rest(text, "struct_member", &smem)
      && (ns.add(smem), true)
      ||
      (text = t2, true)
      && test(strtype = cast(IType) rest(text, "type"))
      && text.bjoin(
        text.gotIdentifier(strname),
        text.accept(","),
        { names ~= strname; types ~= strtype; }
      ) && text.accept(";")
      && {
        foreach (i, strname; names)
          new RelMember(strname, types[i], ns);
        names = null; types = null;
        return true;
      }()
    )
  );
}

Object gotStructDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("struct ")) return null;
  string name;
  Structure st;
  if (t2.gotIdentifier(name) && t2.accept("{")) {
    New(st, name);
    st.sup = namespace();
    if (matchStructBody(t2, st, cont, rest)) {
      if (!t2.accept("}"))
        throw new Exception("Missing closing bracket at "~t2.next_text());
      namespace().add(st);
      text = t2;
      return Single!(NoOp);
    } else {
      throw new Exception("Couldn't match structure body at "~t2.next_text());
    }
  } else return null;
}
mixin DefaultParser!(gotStructDef, "tree.typedef.struct");

import ast.pointer;
class MemberAccess(T) : T {
  T base;
  RelMember stm;
  string name;
  this(T t, string name) {
    base = t;
    this.name = name;
    stm = cast(RelMember) (cast(Namespace) base.valueType()).lookup(name);
    if (!stm) throw new Exception(Format("No ", name, " in ", base.valueType(), "!"));
  }
  mixin defaultIterate!(base);
  override {
    import tools.log;
    string toString() {
      return Format("(", base, ").", name);
    }
    IType valueType() { return stm.type; }
    import tools.base;
    void emitAsm(AsmFile af) {
      auto st = cast(Structure) base.valueType();
      static if (is(T: LValue)) {
        assert(stm.type.size == 4 /or/ 2 /or/ 1,
          Format("Invalid struct member type: ", stm.type));
        af.comment("emit location of ", base, " for member access to ", stm.name, " @", stm.offset);
        base.emitLocation(af);
        af.comment("pop and dereference");
        af.popStack("%eax", new Pointer(st));
        string reg;
        if (stm.type.size == 4) {
          reg = "%eax";
          af.mmove4(Format(stm.offset, "(%eax)"), reg);
        } else if (stm.type.size == 2) {
          reg = "%ax";
          af.mmove2(Format(stm.offset, "(%eax)"), reg);
        } else {
          reg = "%bl";
          af.put("xorw %bx, %bx");
          af.mmove1(Format(stm.offset, "(%eax)"), reg);
        }
        af.comment("push back ", reg);
        af.pushStack(reg, stm.type);
      } else {
        assert(stm.type.size == 4);
        af.comment("emit struct ", base, " for member access");
        base.emitAsm(af);
        af.comment("store member and free: ", stm.name);
        af.mmove4(Format(stm.offset, "(%esp)"), "%eax");
        af.sfree(st.size);
        af.comment("repush member");
        af.pushStack("%eax", stm.type);
      }
    }
    static if (is(T: LValue)) {
      void emitLocation(AsmFile af) {
        if (!af.optimize) af.comment("emit location of ", base, " for member address of ", stm.name, " @", stm.offset);
        base.emitLocation(af);
        if (!af.optimize) af.comment("add offset ", stm.offset);
        af.mathOp("addl", Format("$", stm.offset), "(%esp)");
      }
    }
  }
}

alias MemberAccess!(Expr) MemberAccess_Expr;
alias MemberAccess!(LValue) MemberAccess_LValue;

Expr mkMemberAccess(Expr strct, string name) {
  if (auto lv = cast(LValue) strct)
    return new MemberAccess_LValue(lv, name);
  else
    return new MemberAccess_Expr(strct, name);
}

import ast.parse;
Object gotMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  assert(lhs_partial());
  auto ex = cast(Expr) lhs_partial();
  if (!ex) return null;
  // pointers get dereferenced for struct access
  while (true) {
    if (auto ptr = cast(Pointer) ex.valueType()) {
      ex = new DerefExpr(ex);
    } else break;
  }
  if (!cast(Structure) ex.valueType())
    return null;
  
  string member;
  
  auto pre_ex = ex;
  if (t2.accept(".") && t2.gotIdentifier(member)) {
    auto st = cast(Structure) ex.valueType();
    auto m = st.lookupRel(member, ex);
    ex = cast(Expr) m;
    if (!ex) {
      if (m) error = Format(member, " is not a struct var: ", m);
      else error = Format(member, " is not a member of ", st.name, "!");
      return null;
    }
    text = t2;
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_struct_member");
