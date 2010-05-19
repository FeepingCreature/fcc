module ast.structure;

import ast.types, ast.base, ast.namespace; // yay, more cycles

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
    throw new Exception(Format(name, " is not a member of ", this.name, "!"));
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
}

import ast.pointer;
class MemberAccess(T) : T {
  T base;
  int which;
  this(T t, string name) { base = t; which = (cast(Structure) base.valueType()).lookupMember(name); }
  override {
    Type valueType() {
      return (cast(Structure) base.valueType()).members[which].type;
    }
    void emitAsm(AsmFile af) {
      auto st = cast(Structure) base.valueType();
      static if (is(T: LValue)) {
        assert(st.members[which].type.size == 4);
        base.emitLocation(af);
        af.popStack("%eax", new Pointer(st));
        af.mmove4(Format(st.getMemberOffset(which), "(%eax)"), "%eax");
        af.pushStack("%eax", st.members[which].type);
      } else {
        assert(st.members[which].type.size == 4);
        base.emitAsm(af);
        af.mmove4(Format(st.getMemberOffset(which), "(%esp)"), "%eax");
        af.sfree(st.size);
        af.pushStack("%eax", st.members[which].type);
      }
    }
    static if (is(T: LValue)) {
      void emitLocation(AsmFile af) {
        base.emitLocation(af);
        af.mathOp("addl", Format("$", (cast(Structure) base.valueType()).getMemberOffset(which)), "(%esp)");
      }
    }
  }
}

alias MemberAccess!(Expr) MemberAccess_Expr;
alias MemberAccess!(LValue) MemberAccess_LValue;
