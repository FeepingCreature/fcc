module ast.structure;

import ast.types, ast.base, ast.namespace, parseBase;

import tools.base: ex;
int sum(S, T)(S s, T t) {
  int res;
  foreach (entry; s)
    res += t(entry);
  return res;
}

/// can be transformed into an obj relative to a base
interface RelTransformable {
  Object transform(Expr base);
}

import tools.log;
class StructMember : Named, RelTransformable {
  string name;
  IType type;
  int offset;
  override string getIdentifier() { return name; }
  override Object transform(Expr base) {
    return cast(Object) mkMemberAccess(base, name);
  }
  this(string name, IType type, Structure strct) {
    logln("struct member: ", name, " of ", type);
    this.name = name;
    this.type = type;
    offset = strct.size();
    strct.add(this);
  }
}

class Structure : Namespace, IType, Named {
  mixin TypeDefaults!();
  string name;
  int size() {
    int res;
    select((string, StructMember member) { res += member.type.size; });
    return res;
  }
  this(string name) {
    this.name = name;
  }
  string mangle() { return "struct_"~name; }
  override string getIdentifier() { return name; }
  override string mangle(string name, IType type) { return "struct_"~name~"_"~type.mangle()~"_"~name; }
  override Stuple!(IType, string, int)[] stackframe() {
    Stuple!(IType, string, int)[] res;
    select((string, StructMember member) { res ~= stuple(member.type, member.name, member.offset); });
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
    select((string, StructMember member) { res ~= Format(member.name, ": ", member.type, "; "); });
    return res ~ " }";
  }
}

Object gotStructDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("struct ")) return null;
  string name;
  Structure st;
  string strname; IType strtype;
  if (t2.gotIdentifier(name) && t2.accept("{")) {
    New(st, name);
    st.sup = namespace();
    
    auto backup = namespace();
    namespace.set(st);
    scope(exit) namespace.set(backup);
    
    Named smem;
    string t3;
    string[] names; IType[] types;
    if (
      t2.many(
        (t3 = t2, true)
        && rest(t2, "struct_member", &smem)
        && (st.add(smem), true)
        ||
        (t2 = t3, true)
        && test(strtype = cast(IType) rest(t2, "type"))
        && t2.bjoin(
          t2.gotIdentifier(strname),
          t2.accept(","),
          { names ~= strname; types ~= strtype; }
        ) && t2.accept(";")
        && {
          foreach (i, strname; names)
            new StructMember(strname, types[i], st);
          names = null; types = null;
          return true;
        }()
      ) && t2.accept("}")
    )
    {
      text = t2;
      st.sup.add(st);
      return Single!(NoOp);
    } else {
      throw new Exception("Error matching struct definition at "~t2.next_text());
    }
  } else return null;
}
mixin DefaultParser!(gotStructDef, "tree.typedef.struct");

import ast.pointer;
class MemberAccess(T) : T {
  T base;
  StructMember stm;
  string name;
  this(T t, string name) {
    base = t;
    this.name = name;
    stm = cast(StructMember) (cast(Structure) base.valueType()).lookup(name);
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
        assert(stm.type.size == 4 /or/ 2 /or/ 1);
        af.comment("emit location of ", base, " for member access");
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
        af.comment("store member and free");
        af.mmove4(Format(stm.offset, "(%esp)"), "%eax");
        af.sfree(st.size);
        af.comment("repush member");
        af.pushStack("%eax", stm.type);
      }
    }
    static if (is(T: LValue)) {
      void emitLocation(AsmFile af) {
        af.comment("emit location of ", base, " for member address");
        base.emitLocation(af);
        af.comment("add offset ", stm.offset);
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
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_member");

Object gotStructName(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    if (auto st = cast(Structure) namespace().lookup(id)) {
      text = t2;
      return st;
    }
  }
  return null;
}
mixin DefaultParser!(gotStructName, "type.struct", "4");
