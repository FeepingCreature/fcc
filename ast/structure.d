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

int needsAlignmentStruct(Structure st) {
  int al = 1;
  st.select((string s, RelMember rm) {
    auto ta = needsAlignment(rm.type);
    if (ta > al) al = ta;
  }, &st.rmcache);
  return al;
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
      logln("Untransformed rel member ", this, ": cannot emit. ");
      asm { int 3; }
    }
    mixin defaultIterate!();
    string getIdentifier() { return name; }
    Object transform(Expr base) {
      return fastcast!(Object) (mkMemberAccess(base, name));
    }
  }
  this(string name, IType type, int offset) {
    this.name = name;
    this.type = type;
    this.offset = offset;
  }
  this(string name, IType type, Namespace ns) {
    this(name, type, 0);
    auto st = fastcast!(Structure)~ ns;
    
    string stname;
    if (st) {
      if (st.immutableNow)
        throw new Exception(Format("Cannot add ", this, " to ", st, ": size already used. "));
      if (st.isUnion) offset = 0;
      else offset = st._size();
      stname = st.name;
    } else offset = (fastcast!(IType)~ ns).size();
    
    // alignment
    bool isAligned = true;
    if (st && st.packed) isAligned = false;
    
    if (isAligned) {
      doAlign(offset, type);
      if (st && st.minAlign > 1) offset = roundTo(offset, st.minAlign);
    }
    if (!this.name) this.name = qformat("_anon_struct_member_", st.field.length, "_of_", type.mangle());
    ns.add(this);
  }
  override RelMember dup() { return this; }
}

class Structure : Namespace, RelNamespace, IType, Named, hasRefType {
  mixin TypeDefaults!(true, false);
  string name;
  bool isUnion, packed, isTempStruct;
  /*
    This indicates that we've accessed the struct size.
    Consequentially, it is now cast in lead and may no
    longer be changed by adding new members.
    This prevents the following case:
    struct A { int foo; A meep() { A res; int bogus = 17; return res; } int bar; }
    where the assignment to bogus, combined with the retroactive size change of A,
    overwrites the previously-unknown int bar in meep.
  */
  bool immutableNow;
  int cached_length, cached_size;
  NSCache!(string, RelMember) rmcache;
  Structure dup() {
    auto res = new Structure(name);
    res.sup = sup;
    res.field = field.dup;
    res.rebuildCache();
    res.isUnion = isUnion; res.packed = packed; res.isTempStruct = isTempStruct;
    res.immutableNow = immutableNow;
    res.cached_length = cached_length; res.cached_size = cached_size;
    return res;
  }
  int _size() {
    int res;
    select((string, RelMember member) {
      if (Single!(Void) == member.type) return;
      auto end = member.offset + member.type.size;
      if (end > res) res = end;
    }, &rmcache);
    return res;
  }
  int size() {
    immutableNow = true;
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
    select((string, RelMember member) { if (i++ == offs) res = member; }, &rmcache);
    return res;
  }
  RelMember[] members() { return selectMap!(RelMember, "$"); }
  Structure slice(int from, int to) {
    assert(!isUnion);
    auto res = new Structure(null);
    res.packed = packed;
    res.sup = sup;
    int i;
    select((string, RelMember member) { if (i !< from && i < to) new RelMember(member.name, member.type, res); i++; }, &rmcache);
    return res;
  }
  NSCache!(string) namecache;
  NSCache!(IType) typecache;
  string[] names() { return selectMap!(RelMember, "$.name")(&namecache); }
  IType[] types() { return selectMap!(RelMember, "$.type")(&typecache); }
  int minAlign = 1; // minimal alignment for struct members (4 for C structs)
  this(string name) {
    this.name = name;
  }
  string mangle() {
    if (!name) {
      auto res = "struct_"~name;
      select((string, RelMember member) { res ~= "_" ~ member.type.mangle ~ "_" ~ member.name; }, &rmcache);
      return res;
    }
    return "struct_"~name;
  }
  override {
    IType getRefType() { return new Pointer(this); }
    string getIdentifier() { return name; }
    string mangle(string name, IType type) {
      string type_mangle;
      if (type) type_mangle = type.mangle() ~ "_";
      return sup.mangle(name, null)~"_"~type_mangle~name;
    }
    Stuple!(IType, string, int)[] stackframe() {
      return selectMap!(RelMember, "stuple($.type, $.name, $.offset)");
    }
    Object lookupRel(string str, Expr base) {
      auto res = lookup(str, true);
      if (auto rt = fastcast!(RelTransformable) (res))
        return fastcast!(Object) (rt.transform(base));
      return res;
    }
    int opEquals(IType it) {
      auto str = fastcast!(Structure)~ it;
      return str is this;
    }
    string toString() {
      if (!name) {
        string[] names;
        foreach (elem; field)
          if (auto n = fastcast!(Named) (elem._1)) {
            string id = n.getIdentifier();
            if (auto rm = fastcast!(RelMember) (elem._1))
              id = Format(id, "@", rm.offset);
            names ~= id;
          }
        return Format("{struct ", names.join(", "), "}");
      }
      return name;
    }
    bool isTempNamespace() { return isTempStruct; }
    void __add(string name, Object obj) {
      if (name && lookup(name, true)) {
        throw new Exception(Format("While adding ", obj, ": "
          "already defined in ", this, "!"
        ));
      }
      super.__add(name, obj);
    }
  }
}

TLS!(IType) RefToParentType;
TLS!(Expr delegate(Expr refexpr)) RefToParentModify;

static this() {
  New(RefToParentType, delegate IType() { return null; });
  New(RefToParentModify, delegate Expr delegate(Expr) *() {
    return &(new Stuple!(Expr delegate(Expr)))._0;
  });
}

import ast.modules;
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
      && {
        if (!addsSelf(smem)) ns.add(smem);
        return true;
      }()
      ||
      (text = t2, true)
      && test(strtype = fastcast!(IType)~ rest(text, "type"))
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
  if (!t2.accept("struct")) {
    if (!t2.accept("union"))
      return null;
    isUnion = true;
  }
  string name;
  Structure st;
  if (t2.gotIdentifier(name) && t2.accept("{")) {
    New(st, name);
    st.isUnion = isUnion;
    namespace().add(st); // gotta do this here so the sup is set
    
    auto rtptbackup = RefToParentType();
    scope(exit) RefToParentType.set(rtptbackup);
    RefToParentType.set(new Pointer(st));
    
    auto rtpmbackup = *RefToParentModify();
    scope(exit) *RefToParentModify.ptr() = rtpmbackup;
    *RefToParentModify.ptr() = delegate Expr(Expr baseref) {
      return new DerefExpr(baseref);
    };
    
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
    stm = fastcast!(RelMember) (fastcast!(Namespace) (base.valueType()).lookup(name));
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
      if (auto lv = fastcast!(LValue)~ base) {
        if (stm.type.size <= 16) {
          af.comment("emit location for member access to ", stm.name, " @", stm.offset);
          lv.emitLocation(af);
          af.comment("pop and dereference");
          af.popStack("%eax", nativePtrSize);
          af.comment("push back ", stm.type.size);
          af.pushStack(Format(stm.offset, "(%eax)"), stm.type.size);
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
        // logln("full emit - worrying. ", base, " SELECTING ", stm);
        // asm { int 3; }
        assert(stm.type.size == 1 /or/ 2 /or/ 4 /or/ 8 /or/ 12 /or/ 16, Format("Asked for ", stm, " in ", base.valueType(), "; bad size; cannot get ", stm.type.size(), " from non-lvalue (", !fastcast!(LValue) (base), ") of ", base.valueType().size(), ". "));
        af.comment("emit semi-structure ", base, " for member access");
        auto bvt = base.valueType();
        if (auto rce = fastcast!(RCE)~ base) bvt = rce.from.valueType();
        auto filler = alignStackFor(bvt, af);
        base.emitAsm(af);
        af.comment("store member and free: ", stm.name);
        if (stm.type.size == 1)
          af.mmove1(Format(stm.offset, "(%esp)"), "%dl");
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
        af.sfree(filler);
        af.comment("repush member");
        if (stm.type.size == 16) {
          af.pushStack("%eax", 4);
          af.nvm("%eax");
        }
        if (stm.type.size >= 12) {
          af.pushStack("%ebx", 4);
          af.nvm("%ebx");
        }
        if (stm.type.size >= 8) {
          af.pushStack("%ecx", 4);
          af.nvm("%ecx");
        }
        if (stm.type.size >= 4) {
          af.pushStack("%edx", 4);
          af.nvm("%edx");
        }
        if (stm.type.size == 2) {
          af.pushStack("%dx", 2);
          af.nvm("%dx");
        }
        if (stm.type.size == 1) {
          af.pushStack("%dl", 1);
          af.nvm("%dl");
        }
      }
    }
  }
}

class MemberAccess_LValue : MemberAccess_Expr, LValue {
  int id;
  this(LValue base, string name) {
    super(fastcast!(Expr)~ base, name);
  }
  this() { }
  override {
    MemberAccess_LValue create() { return new MemberAccess_LValue; }
    MemberAccess_LValue dup() { return fastcast!(MemberAccess_LValue) (super.dup()); }
    void emitLocation(AsmFile af) {
      auto st = fastcast!(Structure)~ base.valueType();
      int[] offs;
      if (st) offs = st.selectMap!(RelMember, "$.offset");
      if (!af.optimize) af.comment("emit location for member address of '", stm.name, "' @", stm.offset, " of ", offs);
      (fastcast!(LValue)~ base).emitLocation(af);
      if (!af.optimize) af.comment("add offset ", stm.offset);
      af.mathOp("addl", Format("$", stm.offset), "(%esp)");
    }
  }
}

import ast.fold, ast.casting;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto r = fastcast!(RCE) (it)) {
      if (auto lit = fastcast!(StructLiteral)~ r.from) {
        if (lit.exprs.length == 1 &&
            lit.exprs[0].valueType() == r.to)
          return fastcast!(Itr) (lit.exprs[0]); // pointless keeping a cast
      }
    }
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto mae = fastcast!(MemberAccess_Expr) (it)) {
      auto base = foldex(mae.base);
      // logln("::", mae.stm.type.size, " vs. ", base.valueType().size);
      if (mae.stm.type.size == base.valueType().size) {
        return fastcast!(Iterable) (reinterpret_cast(mae.stm.type, base));
      }
      
      {
        Expr from;
        if (auto mae2 = fastcast!(MemberAccess_Expr)~ base) from = base; // lol direct
        if (auto c = fastcast!(RCL) (base)) from = foldex(c.from);
        if (auto c = fastcast!(RCE) (base)) from = foldex(c.from);
        if (from) {
          if (auto m2 = fastcast!(MemberAccess_Expr)~ from) {
            MemberAccess_Expr weird;
            if (fastcast!(MemberAccess_LValue) (from)) weird = new MemberAccess_LValue;
            else New(weird);
            weird.base = m2.base;
            weird.stm = new RelMember(null, mae.stm.type, mae.stm.offset + m2.stm.offset);
            return fastcast!(Iterable) (weird);
          }
        }
      }
      
      Structure st;
      if (auto rce = fastcast!(RCE)~ base) {
        base = rce.from;
        st = fastcast!(Structure)~ rce.to;
      }
      
      if (auto sl = fastcast!(StructLiteral)~ base) {
        Expr res;
        int i;
        if (!st)
          st = fastcast!(Structure)~ base.valueType();
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
        }, &st.rmcache);
        return fastcast!(Iterable) (res); // may be null - that's okay!
      }
    }
    return null;
  };
  alignChecks ~= (IType it) {
    if (auto st = fastcast!(Structure) (it))
      return needsAlignmentStruct(st);
    return 0;
  };
}

Expr mkMemberAccess(Expr strct, string name) {
  if (auto lv = fastcast!(LValue)~ strct) return new MemberAccess_LValue(lv, name);
  else                              return new MemberAccess_Expr  (strct, name);
}

Expr depointer(Expr ex) {
  while (true) {
    if (auto ptr = fastcast!(Pointer) (resolveType(ex.valueType()))) {
      ex = new DerefExpr(ex);
    } else break;
  }
  return ex;
}

extern(C) bool _isITemplate(Object obj);

import ast.parse, ast.fun, tools.base: or;
Object gotMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  assert(lhs_partial());
  auto first_ex = fastcast!(Expr)~ lhs_partial();
  Expr ex;
  Expr[] alts;
  IType[] spaces;
  auto t2 = text;
  if (first_ex) {
    ex = first_ex;
    auto ex3 = ex;
    gotImplicitCast(ex3, (Expr ex) {
      {
        auto vt = ex.valueType();
        if (auto srn = fastcast!(SemiRelNamespace) (vt))
          vt = fastcast!(IType) (srn.resolve());
        if (auto rn = fastcast!(RelNamespace) (vt)) {
          alts ~= ex;
          spaces ~= vt;
        }
      }
      auto ex4 = depointer(ex);
      if (ex4 !is ex) {
        gotImplicitCast(ex4, (Expr ex) {
          auto vt = ex.valueType();
          if (auto srn = fastcast!(SemiRelNamespace) (vt))
            vt = fastcast!(IType) (srn.resolve());
          if (auto rn = fastcast!(RelNamespace) (vt)) {
            alts ~= ex;
            spaces ~= vt;
          }
          return false;
        });
      }
      return false;
    });
  } else {
    if (auto ty = fastcast!(IType) (lhs_partial())) {
      auto vt = resolveType(ty);
      if (auto srn = fastcast!(SemiRelNamespace) (vt))
        vt = fastcast!(IType) (srn.resolve());
      
      if (fastcast!(Namespace) (vt) || fastcast!(RelNamespace) (vt)) {
        alts ~= null;
        spaces ~= vt;
      }
    }
  }
  if (!alts.length) {
    return null;
  }
  
  string member;
  
  if (t2.gotIdentifier(member)) {
    
  try_next_alt:
    if (!alts.length)
      return null;
    ex = alts[0]; alts = alts[1 .. $];
    auto space = spaces[0]; spaces = spaces[1 .. $];
    
    auto pre_ex = ex;
    
    auto rn = fastcast!(RelNamespace) (space);
  retry:
    if (!ex) {
      auto ns = fastcast!(Namespace) (space);
      Object m;
      if (rn) m = rn.lookupRel(member, null);
      else if (ns) m = ns.lookup(member, true);
      if (!m) goto try_next_alt;
      
      // auto ex2 = fastcast!(Expr) (m);
      // if (!ex2) {
      if (!m) {
        if (t2.eatDash(member)) goto retry;
        text.setError(Format("No ", member, " in ", ns, "!"));
        goto try_next_alt;
      }
      
      text = t2;
      return m;
    }
    auto m = rn.lookupRel(member, ex);
    if (!m) {
      if (t2.eatDash(member)) goto retry;
      string mesg, name;
      auto info = Format(pre_ex.valueType());
      if (info.length > 64) info = info[0..64] ~ " [snip]";
      if (auto st = fastcast!(Structure) (resolveType(fastcast!(IType) (rn)))) {
        name = st.name;
        /*logln("alts1 ");
        foreach (i, alt; alts)
          logln("  ", i, ": ", alt);*/
        mesg = Format(member, " is not a member of ", pre_ex.valueType(), ", containing ", st.names);
      } else {
        /*logln("alts2: ");
        foreach (i, alt; alts)
          logln("  ", i, ": ", alt);*/
        mesg = Format(member, " is not a member of non-struct ", info);
      }
      text.setError(mesg);
      goto try_next_alt;
    }
    text = t2;
    return m;
  } else return null;
}
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_rel_member", null, ".");

static this() {
  typeModlist ~= delegate IType(ref string text, IType cur, ParseCb, ParseCb) {
    Object nscur = fastcast!(Object) (resolveType(cur));
    while (true) {
      if (auto srn = fastcast!(SemiRelNamespace) (nscur)) {
        nscur = fastcast!(Object) (srn.resolve());
        continue;
      }
      break;
    }
    
    auto ns = fastcast!(Namespace) (nscur);
    if (!ns) return null;
    
    auto t2 = text;
    if (!t2.accept(".")) return null;
    
    string id;
    if (!t2.gotIdentifier(id)) return null;
    retry:
      // logln("Try to ", id, " into ", ns);
      // logln(" => ", ns.lookup(id), ", left ", t2.nextText());
      if (auto ty = fastcast!(IType) (ns.lookup(id))) {
        // logln("return ", ty);
        text = t2;
        return ty;
      }
      if (t2.eatDash(id)) goto retry;
    return null;
  };
}
