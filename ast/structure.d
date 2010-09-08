module ast.structure;

import ast.types, ast.base, ast.namespace, ast.vardecl, ast.int_literal, parseBase;

import tools.base: ex, This, This_fn, rmSpace;
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

int needsAlignmentStruct(Structure st) {
  int al = 1;
  foreach (type; st.types) {
    auto ta = needsAlignment(type);
    if (ta > al) al = ta;
  }
  return al;
}

int needsAlignment(IType it) {
  if (auto st = cast(Structure) it) return needsAlignmentStruct(st);
  const limit = 4;
  if (it.size > limit) return limit;
  else return it.size;
}

void doAlign(ref int offset, IType type) {
  int to = needsAlignment(type);
  offset = roundTo(offset, to);
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
  this(string name, IType type, int offset) {
    this.name = name;
    this.type = type;
    this.offset = offset;
  }
  this(string name, IType type, Namespace ns) {
    this(name, type, 0);
    auto st = cast(Structure) ns;
    
    if (st) {
      if (st.isUnion) offset = 0;
      else offset = st._size();
    } else offset = (cast(IType) ns).size();
    
    // alignment
    bool isAligned = true;
    if (st && st.packed) isAligned = false;
    
    if (isAligned)
      doAlign(offset, type);
    
    ns.add(this);
  }
  override RelMember dup() { return this; }
}

class Structure : Namespace, RelNamespace, IType, Named {
  mixin TypeDefaults!();
  string name;
  bool isUnion;
  bool packed;
  int _size() {
    int res;
    select((string, RelMember member) {
      auto end = member.offset + member.type.size;
      if (end > res) res = end;
    });
    return res;
  }
  int size() {
    auto res = _size(); //, pre = res;
    doAlign(res, this);
    // if (res != pre) logln(pre, " -> ", res, ": ", this);
    return res;
  }
  RelMember selectMember(int offs) {
    int i;
    RelMember res;
    select((string, RelMember member) { if (i++ == offs) res = member; });
    return res;
  }
  RelMember[] members() {
    RelMember[] res;
    select((string, RelMember member) { res ~= member; });
    return res;
  }
  Structure slice(int from, int to) {
    assert(!isUnion);
    auto res = new Structure(null);
    res.packed = packed;
    int i;
    select((string, RelMember member) { if (i !< from && i < to) new RelMember(member.name, member.type, res); i++; });
    return res;
  }
  string[] names() {
    string[] res;
    select((string, RelMember member) { res ~= member.name; });
    return res;
  }
  IType[] types() {
    IType[] res;
    select((string, RelMember member) { res ~= member.type; });
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
      // logln("struct rel base is ", base);
      auto res = lookup(str);
      if (auto rt = cast(RelTransformable) res)
        return cast(Object) rt.transform(base);
      return res;
    }
    string toString() {
      string res = "struct ";
      if (name) res ~= name;
      else res ~= Format(cast(void*) this);
      string res2;
      select((string, RelMember member) {
        if (res2.length) res2 ~= ", ";
        if (member.name) res2 ~= member.name;
        else res2 ~= Format(member.type);
        res2 ~= Format(" ", member.type.size, "@", member.offset);
      });
      return res ~ " { " ~ res2 ~ " }";
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
      && { if (!addsSelf(smem)) ns.add(smem); return true; }()
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
  bool isUnion;
  if (!t2.accept("struct ")) {
    if (!t2.accept("union "))
      return null;
    isUnion = true;
  }
  string name;
  Structure st;
  if (t2.gotIdentifier(name) && t2.accept("{")) {
    New(st, name);
    st.isUnion = isUnion;
    namespace().add(st); // gotta do this here so the sup is set
    if (matchStructBody(t2, st, cont, rest)) {
      if (!t2.accept("}"))
        throw new Exception("Missing closing struct bracket at "~t2.next_text());
      text = t2;
      return Single!(NoOp);
    } else {
      throw new Exception("Couldn't match structure body at "~t2.next_text());
    }
  } else return null;
}
mixin DefaultParser!(gotStructDef, "tree.typedef.struct");

class StructLiteral : Expr {
  Structure st;
  Expr[] exprs;
  this(Structure st, Expr[] exprs...) {
    this.st = st;
    foreach (ex; exprs) assert(ex);
    this.exprs = exprs.dup;
  }
  private this() { }
  mixin defaultIterate!(exprs);
  override {
    string toString() { return Format("literal ", st, " {", exprs, "}"); }
    StructLiteral dup() {
      auto res = new StructLiteral;
      res.st = st;
      res.exprs = exprs.dup;
      foreach (ref entry; res.exprs) entry = entry.dup;
      return res;
    }
    IType valueType() { return st; }
    void emitAsm(AsmFile af) {
      auto sf = st.stackframe();
      mixin(mustOffset("st.size"));
      int offset;
      // structs are pushed on the stack in reverse order.
      // This makes things .. complicated.
      foreach_reverse (i, entry; sf) {
        auto rev_offs = st.size - entry._2 - entry._0.size; // end of variable
        if (rev_offs > offset) {
          af.salloc(rev_offs - offset);
          offset = rev_offs;
        }
        auto ex = exprs[i];
        if (ex.valueType() != entry._0)
          throw new Exception(Format("Cannot use ", ex, " in struct literal: doesn't match ", entry._0, "!"));
        {
          mixin(mustOffset("ex.valueType().size"));
          ex.emitAsm(af);
        }
        offset += ex.valueType().size;
      }
    }
  }
}

import ast.pointer;
class MemberAccess_Expr : Expr {
  // be warned: if this is constructed manually, does _not_ have to be a struct!
  // this specifically applies when optimizing away recursive member accesses,
  // in which case this may become a RelMember access to .. any type.
  Expr base;
  RelMember stm;
  string name;
  this(Expr base, string name) {
    this.base = base;
    this.name = name;
    stm = cast(RelMember) (cast(Namespace) base.valueType()).lookup(name);
    if (!stm) throw new Exception(Format("No ", name, " in ", base.valueType(), "!"));
  }
  this() { }
  MemberAccess_Expr create() { return new MemberAccess_Expr; }
  MemberAccess_Expr dup() {
    auto res = create();
    res.base = base.dup;
    res.stm = stm.dup;
    res.name = name;
    return res;
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
      auto st = base.valueType();
      if (auto lv = cast(LValue) base) {
        if (stm.type.size == 4 /or/ 2 /or/ 1) {
          af.comment("emit location of ", lv, " for member access to ", stm.name, " @", stm.offset);
          lv.emitLocation(af);
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
          mkVar(af, stm.type, true, (Variable var) {
            iparse!(Statement, "copy_struct_member", "tree.semicol_stmt.expr")
            ("memcpy(cast(void*) &tempvar, (cast(void*) &var) + offset, size)",
              "tempvar", var,
              "var", lv,
              "size", new IntExpr(stm.type.size),
              "offset", new IntExpr(stm.offset)
            ).emitAsm(af);
          });
        }
      } else {
        // if (stm.type.size != 4) asm { int 3; }
        assert(stm.type.size == 4 /or/ 8, Format("Asked for ", stm, " in ", base.valueType(), "; bad size; cannot get ", stm.type.size(), " from non-lvalue (", !cast(LValue) base, ") of ", base.valueType().size(), ". "));
        af.comment("emit semi-structure ", base, " for member access");
        base.emitAsm(af);
        af.comment("store member and free: ", stm.name);
        af.mmove4(Format(stm.offset, "(%esp)"), "%eax");
        if (stm.type.size == 8)
          af.mmove4(Format(stm.offset + 4, "(%esp)"), "%ebx");
        af.sfree(st.size);
        af.comment("repush member");
        if (stm.type.size == 8)
          af.pushStack("%ebx", Single!(SysInt));
        af.pushStack("%eax", Single!(SysInt));
      }
    }
  }
}

class MemberAccess_LValue : MemberAccess_Expr, LValue {
  this(LValue base, string name) {
    super(cast(Expr) base, name);
  }
  this() { }
  override {
    MemberAccess_LValue create() { return new MemberAccess_LValue; }
    MemberAccess_LValue dup() { return cast(MemberAccess_LValue) super.dup(); }
    void emitLocation(AsmFile af) {
      if (!af.optimize) af.comment("emit location of ", base, " for member address of ", stm.name, " @", stm.offset);
      (cast(LValue) base).emitLocation(af);
      if (!af.optimize) af.comment("add offset ", stm.offset);
      af.mathOp("addl", Format("$", stm.offset), "(%esp)");
    }
  }
}

import ast.fold, ast.casting;
static this() {
  foldopt ~= delegate Expr(Expr ex) {
    if (auto mae = cast(MemberAccess_Expr) ex) {
      auto base = fold(mae.base);
      // logln("::", mae.stm.type.size, " vs. ", base.valueType().size);
      if (mae.stm.type.size == base.valueType().size) {
        if (auto lv = cast(LValue) base)
          return new RCL(mae.stm.type, lv);
        else
          return new RCE(mae.stm.type, base);
      }
    }
    return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto mae = cast(MemberAccess_Expr) ex) {
      auto base = fold(mae.base);
      if (auto sl = cast(StructLiteral) base) {
        Expr res;
        int i;
        auto st = cast(Structure) base.valueType();
        if (st) st.select((string, RelMember member) {
          if (member is mae.stm)
            res = sl.exprs[i];
          i++;
        });
        return res; // may be null - that's okay!
      }
    }
    return null;
  };
  foldopt ~= delegate Expr(Expr ex) {
    if (auto mae = cast(MemberAccess_Expr) ex) {
      auto base = fold(mae.base);
      Expr from;
      if (auto mae2 = cast(MemberAccess_Expr) base) from = base; // lol direct
      if (auto c = cast(RCL) base) from = fold(c.from);
      if (auto c = cast(RCE) base) from = fold(c.from);
      if (from) {
        if (auto m2 = cast(MemberAccess_Expr) from) {
          MemberAccess_Expr weird;
          if (cast(MemberAccess_LValue) from) weird = new MemberAccess_LValue;
          else New(weird);
          weird.base = m2.base;
          weird.stm = new RelMember(null, mae.stm.type, mae.stm.offset + m2.stm.offset);
          return weird;
        }
      }
    }
    return null;
  };
}

Expr mkMemberAccess(Expr strct, string name) {
  if (auto lv = cast(LValue) strct) return new MemberAccess_LValue(lv, name);
  else                              return new MemberAccess_Expr  (strct, name);
}

Expr depointer(Expr ex) {
  while (true) {
    if (auto ptr = cast(Pointer) ex.valueType()) {
      ex = new DerefExpr(ex);
    } else break;
  }
  return ex;
}

import ast.parse, tools.base: or;
Object gotMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  assert(lhs_partial());
  auto ex = cast(Expr) lhs_partial();
  if (!ex) return null;
  // pointers get dereferenced for struct access
  ex = depointer(ex);
  if (!gotImplicitCast(ex, (IType it) { return !!cast(Structure) it; }))
    return null;
  
  string member;
  
  auto pre_ex = ex;
  if (t2.accept(".") && t2.gotIdentifier(member)) {
    auto st = cast(Structure) ex.valueType();
    auto m = st.lookupRel(member, ex);
    ex = cast(Expr) m;
    if (!ex) {
      if (m) error = Format(member, " is not a struct var: ", m);
      else {
        error = Format(member, " is not a member of ", st.name, ", containing ", st.names, "!");
        if (member != "toDg" /or/ "stringof" /or/ "onUsing" /or/ "onExit") // list of keywords
          throw new Exception(error);
      }
      return null;
    }
    text = t2;
    return cast(Object) ex;
  } else return null;
}
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_struct_member");
