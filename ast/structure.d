module ast.structure;

import ast.types, ast.base, ast.namespace, ast.vardecl, ast.int_literal, parseBase;

import tools.base: ex, This, This_fn, rmSpace, join;
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
  st.select((string s, RelMember rm) {
    auto ta = needsAlignment(rm.type);
    if (ta > al) al = ta;
  });
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
    
    string stname;
    if (st) {
      if (st.isUnion) offset = 0;
      else offset = st._size();
      stname = st.name;
    } else offset = (cast(IType) ns).size();
    
    // alignment
    bool isAligned = true;
    if (st && st.packed) isAligned = false;
    
    if (isAligned)
      doAlign(offset, type);
    if (!this.name) this.name = qformat("_anon_struct_member_", st.field.length);
    ns.add(this);
  }
  override RelMember dup() { return this; }
}

class Structure : Namespace, RelNamespace, IType, Named, hasRefType {
  mixin TypeDefaults!(true, false);
  string name;
  bool isUnion, packed, isTempStruct;
  int cached_length, cached_size;
  int _size() {
    int res;
    select((string, RelMember member) {
      if (Single!(Void) == member.type) return;
      auto end = member.offset + member.type.size;
      if (end > res) res = end;
    });
    return res;
  }
  int size() {
    if (field.length == cached_length)
      if (cached_size) return cached_size;
    auto res = _size(); //, pre = res;
    doAlign(res, this);
    // if (res != pre) logln(pre, " -> ", res, ": ", this);
    cached_size = res;
    cached_length = field.length;
    return res;
  }
  RelMember selectMember(int offs) {
    int i;
    RelMember res;
    select((string, RelMember member) { if (i++ == offs) res = member; });
    return res;
  }
  RelMember[] members() { return selectMap!(RelMember, "$"); }
  Structure slice(int from, int to) {
    assert(!isUnion);
    auto res = new Structure(null);
    res.packed = packed;
    int i;
    select((string, RelMember member) { if (i !< from && i < to) new RelMember(member.name, member.type, res); i++; });
    return res;
  }
  string[] names() { return selectMap!(RelMember, "$.name")(); }
  IType[] types() { return selectMap!(RelMember, "$.type")(); }
  this(string name) {
    this.name = name;
  }
  string mangle() {
    if (!name) {
      auto res = "struct_"~name;
      select((string, RelMember member) { res ~= "_" ~ member.type.mangle ~ "_" ~ member.name; });
      return res;
    }
    return "struct_"~name;
  }
  override {
    IType getRefType() { return new Pointer(this); }
    string getIdentifier() { return name; }
    string mangle(string name, IType type) { return "struct_"~name~"_"~type.mangle()~"_"~name; }
    Stuple!(IType, string, int)[] stackframe() {
      return selectMap!(RelMember, "stuple($.type, $.name, $.offset)");
    }
    Object lookupRel(string str, Expr base) {
      // logln("struct rel base is ", base);
      auto res = lookup(str);
      if (auto rt = cast(RelTransformable) res)
        return cast(Object) rt.transform(base);
      return res;
    }
    int opEquals(IType it) {
      auto str = cast(Structure) it;
      return str is this;
    }
    string toString() {
      if (!name) {
        string[] names;
        foreach (elem; field) if (auto n = cast(Named) elem._1) names ~= n.getIdentifier();
        return Format("{struct ", names.join(", "), "}");
      }
      return name;
    }
    bool isTempNamespace() { return isTempStruct; }
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
        t2.failparse("Missing closing struct bracket");
      text = t2;
      return Single!(NoOp);
    } else {
      t2.failparse("Couldn't match structure body");
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
          auto type = ex.valueType(), size = (Single!(Void) == type)?0:type.size;
          mixin(mustOffset("size"));
          ex.emitAsm(af);
        }
        offset += ex.valueType().size;
      }
    }
  }
}

import ast.pointer;
class MemberAccess_Expr : Expr, HasInfo {
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
  string getInfo() { return "."~name; }
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
        if (stm.type.size <= 16) {
          af.comment("emit location for member access to ", stm.name, " @", stm.offset);
          lv.emitLocation(af);
          af.comment("pop and dereference");
          af.popStack("%eax", new Pointer(st));
          af.comment("push back ", stm.type.size);
          af.pushStack(Format(stm.offset, "(%eax)"), stm.type);
          af.nvm("%eax");
        } else {
          mkVar(af, stm.type, true, (Variable var) {
            iparse!(Statement, "copy_struct_member", "tree.semicol_stmt.expr")
            ("memcpy(tempvarp, varp + offset, size)",
              "tempvarp", reinterpret_cast(voidp, new RefExpr(var)),
              "varp", reinterpret_cast(voidp, new RefExpr(lv)),
              "size", mkInt(stm.type.size),
              "offset", mkInt(stm.offset)
            ).emitAsm(af);
          });
        }
      } else {
        // if (stm.type.size != 4) asm { int 3; }
        assert(stm.type.size == 2 /or/ 4 /or/ 8 /or/ 12 /or/ 16, Format("Asked for ", stm, " in ", base.valueType(), "; bad size; cannot get ", stm.type.size(), " from non-lvalue (", !cast(LValue) base, ") of ", base.valueType().size(), ". "));
        af.comment("emit semi-structure ", base, " for member access");
        base.emitAsm(af);
        af.comment("store member and free: ", stm.name);
        if (stm.type.size == 2)
          af.mmove2(Format(stm.offset, "(%esp)"), "%dx");
        if (stm.type.size >= 4)
          af.mmove4(Format(stm.offset, "(%esp)"), "%edx");
        if (stm.type.size >= 8)
          af.mmove4(Format(stm.offset + 4, "(%esp)"), "%ecx");
        if (stm.type.size >= 12)
          af.mmove4(Format(stm.offset + 8, "(%esp)"), "%ebx");
        if (stm.type.size == 16)
          af.mmove4(Format(stm.offset + 12, "(%esp)"), "%eax");
        af.sfree(st.size);
        af.comment("repush member");
        if (stm.type.size == 16) {
          af.pushStack("%eax", Single!(SysInt));
          af.nvm("%eax");
        }
        if (stm.type.size >= 12) {
          af.pushStack("%ebx", Single!(SysInt));
          af.nvm("%ebx");
        }
        if (stm.type.size >= 8) {
          af.pushStack("%ecx", Single!(SysInt));
          af.nvm("%ecx");
        }
        if (stm.type.size >= 4) {
          af.pushStack("%edx", Single!(SysInt));
          af.nvm("%edx");
        }
        if (stm.type.size == 2) {
          af.pushStack("%dx", Single!(Short));
          af.nvm("%dx");
        }
      }
    }
  }
}

class MemberAccess_LValue : MemberAccess_Expr, LValue {
  int id;
  this(LValue base, string name) {
    super(cast(Expr) base, name);
  }
  this() { }
  override {
    MemberAccess_LValue create() { return new MemberAccess_LValue; }
    MemberAccess_LValue dup() { return cast(MemberAccess_LValue) super.dup(); }
    void emitLocation(AsmFile af) {
      auto st = cast(Structure) base.valueType();
      int[] offs;
      if (st) offs = st.selectMap!(RelMember, "$.offset");
      if (!af.optimize) af.comment("emit location for member address of '", stm.name, "' @", stm.offset, " of ", offs);
      (cast(LValue) base).emitLocation(af);
      if (!af.optimize) af.comment("add offset ", stm.offset);
      af.mathOp("addl", Format("$", stm.offset), "(%esp)");
    }
  }
}

import ast.fold, ast.casting;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto r = cast(RCE) it) {
      if (auto lit = cast(StructLiteral) r.from) {
        if (lit.exprs.length == 1 &&
            lit.exprs[0].valueType() == r.to)
          return lit.exprs[0]; // pointless keeping a cast
      }
    }
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto mae = cast(MemberAccess_Expr) it) {
      auto base = foldex(mae.base);
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
  foldopt ~= delegate Itr(Itr it) {
    if (auto mae = cast(MemberAccess_Expr) it) {
      auto base = foldex(mae.base);
      Structure st;
      if (auto rce = cast(RCE) base) {
        base = rce.from;
        st = cast(Structure) rce.to;
      }
      if (auto sl = cast(StructLiteral) base) {
        Expr res;
        int i;
        if (!st)
          st = cast(Structure) base.valueType();
        else {
          // TODO: assert: struct member offsets identical!
        }
        if (st) st.select((string, RelMember member) {
          if (member is mae.stm) {
            res = sl.exprs[i];
            if (mae.valueType() != res.valueType())
              logln("Type mismatch: ", mae.valueType(), " vs. ", res.valueType());
          }
          i++;
        });
        return res; // may be null - that's okay!
      }
    }
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto mae = cast(MemberAccess_Expr) it) {
      auto base = foldex(mae.base);
      Expr from;
      if (auto mae2 = cast(MemberAccess_Expr) base) from = base; // lol direct
      if (auto c = cast(RCL) base) from = foldex(c.from);
      if (auto c = cast(RCE) base) from = foldex(c.from);
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

import ast.parse, ast.fun, tools.base: or;
Object gotMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  assert(lhs_partial());
  auto ex = cast(Expr) lhs_partial();
  if (!ex) return null;
  // pointers get dereferenced for struct access
  ex = depointer(ex);
  if (!gotImplicitCast(ex, (IType it) { return !!cast(RelNamespace) it; }))
    return null;
  
  string member;
  
  auto pre_ex = ex;
  if (t2.gotIdentifier(member)) {
    auto rn = cast(RelNamespace) ex.valueType();
    retry:
    auto m = rn.lookupRel(member, ex);
    if (cast(Function) m) { text = t2; return m; }
    auto ex2 = cast(Expr) m;
    if (!ex2) {
      if (m) text.setError(member, " is not a rel var: ", m);
      else {
        if (t2.eatDash(member)) goto retry;
        string mesg, name;
        bool dontFail;
        if (auto st = cast(Structure) rn) {
          name = st.name;
          mesg = Format(member, " is not a member of ", pre_ex.valueType(), ", containing ", st.names);
        } else {
          mesg = Format(member, " is not a member of ", pre_ex.valueType());
        }
        if (rn.isTempNamespace) dontFail = true;
        
        if (!dontFail && member != "toDg" /or/ "stringof" /or/ "onUsing" /or/ "onExit" /or/ "eval" /or/ "ptr" /or/ "length" /or/ "lensq" /or/ "sum" // list of keywords
          && (!name || !name.startsWith("__array_as_struct__")))
          text.failparse(mesg);
        else
          text.setError(mesg);
      }
      return null;
    }
    text = t2;
    return cast(Object) ex2;
  } else return null;
}
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_rel_member", null, ".");
