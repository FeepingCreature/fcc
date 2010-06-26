module ast.structure;

import ast.types, ast.base, ast.namespace, parseBase;

import tools.base: ex;
int sum(S, T)(S s, T t) {
  int res;
  foreach (entry; s)
    res += t(entry);
  return res;
}

class Structure : Type {
  string name;
  struct Member {
    string name;
    Type type;
  }
  Member[] members;
  int lookupMember(string name) {
    foreach (i, m; members) if (m.name == name) return i;
    return -1;
  }
  int getMemberOffset(int id) {
    int offs;
    foreach (member; members[0 .. id]) offs += member.type.size;
    return offs;
  }
  override int size() {
    return members.sum(ex!("t -> t.type.size()"));
  }
  this(string name, Member[] members) {
    this.name = name;
    this.members = members;
  }
  override string mangle() { return "struct_"~name; }
  string toString() {
    auto res = super.toString() ~ " { ";
    foreach (member; members) res ~= Format(member.name, ": ", member.type, "; ");
    return res ~ " }";
  }
}

Object gotStructDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("struct ")) return null;
  string name;
  Structure.Member[] ms;
  Structure.Member sm;
  if (t2.gotIdentifier(name) && t2.accept("{") &&
      t2.many(
        test(sm.type = cast(Type) rest(t2, "type")) &&
        t2.bjoin(
          t2.gotIdentifier(sm.name),
          t2.accept(",")
          ,{ ms ~= sm; }
        ) &&
        t2.accept(";")
      ) &&
      t2.accept("}")
    )
  {
    text = t2;
    auto st = new Structure(name, ms);
    namespace().add(st);
    return Single!(NoOp);
  } else return null;
}
mixin DefaultParser!(gotStructDef, "tree.typedef.struct");

import ast.pointer;
class MemberAccess(T) : T {
  T base;
  int which;
  string name;
  this(T t, string name) {
    base = t;
    this.name = name;
    which = (cast(Structure) base.valueType()).lookupMember(name);
    if (which == -1) throw new Exception(Format("No ", name, " in ", base.valueType(), "!"));
  }
  mixin defaultIterate!(base);
  override {
    import tools.log;
    string toString() {
      return Format("(", base, ").", name);
    }
    Type valueType() {
      return (cast(Structure) base.valueType()).members[which].type;
    }
    void emitAsm(AsmFile af) {
      auto st = cast(Structure) base.valueType();
      static if (is(T: LValue)) {
        assert(st.members[which].type.size == 4);
        af.comment("emit location of ", base, " for member access");
        base.emitLocation(af);
        af.comment("pop and dereference");
        af.popStack("%eax", new Pointer(st));
        af.mmove4(Format(st.getMemberOffset(which), "(%eax)"), "%eax");
        af.comment("push back");
        af.pushStack("%eax", st.members[which].type);
      } else {
        assert(st.members[which].type.size == 4);
        af.comment("emit struct ", base, " for member access");
        base.emitAsm(af);
        af.comment("store member and free");
        af.mmove4(Format(st.getMemberOffset(which), "(%esp)"), "%eax");
        af.sfree(st.size);
        af.comment("repush member");
        af.pushStack("%eax", st.members[which].type);
      }
    }
    static if (is(T: LValue)) {
      void emitLocation(AsmFile af) {
        af.comment("emit location of ", base, " for member address");
        base.emitLocation(af);
        auto offs = (cast(Structure) base.valueType()).getMemberOffset(which);
        af.comment("add offset ", offs);
        af.mathOp("addl", Format("$", offs), "(%esp)");
      }
    }
  }
}

alias MemberAccess!(Expr) MemberAccess_Expr;
alias MemberAccess!(LValue) MemberAccess_LValue;

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
    if (st.lookupMember(member) == -1) {
      error = Format(member, " is not a member of ", st.name, "!");
      return null;
    }
    if (auto lv = cast(LValue) ex)
      ex = new MemberAccess_LValue(lv, member);
    else
      ex = new MemberAccess_Expr(ex, member);
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

class NestedCall : FunCall {
  override void emitAsm(AsmFile af) {
    callNested(af, fun.type.ret, params, fun.mangleSelf, new Register!("ebp"));
  }
  override Type valueType() {
    return fun.type.ret;
  }
}

class StructMemberFunction : Function {
  Expr strct;
  this(Expr ex) {
    strct = ex;
    assert(!!cast(Structure) strct.valueType());
  }
  mixin defaultIterate(strct);
  override {
    string mangleSelf() {
      return (strct.valueType()).mangleSelf() ~ "_" ~ super.mangleSelf();
    }
    string mangle(string name, Type type) {
      return mangleSelf() ~ "_" ~ type.mangle(name);
    }
    FunCall mkCall() {
      return new MemberCall;
    }
    int fixup() {
      auto cur = super.fixup();
      add(new Variable(Single!(Pointer, Single!(Void)), "__base_ptr", cur));
      return cur + 4;
    }
    Object lookup(string name, bool local = false) { return lookup(name, local, null, null); }
  }
  import tools.log;
  Object lookup(string name, bool local, Expr mybase) {
    { // local lookup first
      Object res;
      if (context_override) res = context_override.lookup(name, true);
      else res = super.lookup(name, true);
      auto var = cast(Variable) res;
      if (mybase && var) {
        return new MemberAccess_LValue(
          namespaceToStruct(context_override?context_override:this, mybase),
          var.name
        );
      } else if (res) return res;
    }
    if (local
     || name == "__base_ptr"
     || name == "__old_ebp"
     || name == "__fun_ret") return null; // never recurse those
    assert(!!context);
    
    if (auto nf = cast(NestedFunction) context.fun) {
      return nf.lookup(name, false, cast(Expr) lookup("__base_ptr", true, mybase), context);
    } else {
      auto sn = context.lookup(name),
            var = cast(Variable) sn;
      if (!var) return sn;
      return new MemberAccess_LValue(
        namespaceToStruct(context, cast(Expr) lookup("__base_ptr", true, mybase)),
        var.name
      );
    }
  }
}
