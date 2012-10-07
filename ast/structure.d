module ast.structure;

import ast.types, ast.base, ast.namespace, ast.vardecl,
  ast.static_arrays, ast.int_literal, parseBase;

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
    string toString() { return Format("["[], name, ": "[], type, " @"[], offset, "]"[]); }
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      logln("Untransformed rel member "[], this, ": cannot emit. "[]);
      fail;
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
        throw new Exception(Format("Cannot add "[], this, " to "[], st, ": size already used. "[]));
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
    if (!this.name) this.name = qformat("_anon_struct_member_"[], st.field.length, "_of_"[], type.mangle());
    ns.add(this);
  }
  override RelMember dup() { return this; }
}

class RelMemberLV : RelMember, LValue {
  void emitLocation(LLVMFile lf) {
    logln("Untransformed rel member "[], this, ": cannot emit location. "[]);
    fail;
  }
  RelMemberLV dup() { return new RelMemberLV(name, type, offset); }
  this(string name, IType type, int offs) { super(name, type, offs); }
  this(string name, IType type, Namespace ns) { super(name, type, ns); }
}

extern(C) Expr _make_tupleof(Structure str, Expr ex);
class Structure : Namespace, RelNamespace, IType, Named, hasRefType, Importer, SelfAdding {
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
  mixin ImporterImpl!();
  NSCache!(string, RelMember) rmcache;
  override {
    bool addsSelf() { return true; }
    bool isPointerLess() {
      bool pointerless = true;
      select((string, RelMember member) { pointerless &= member.type.isPointerLess(); });
      return pointerless;
    }
    bool isComplete() {
      bool complete = true;
      select((string, RelMember member) { complete &= member.type.isComplete(); });
      return complete;
    }
    bool returnsInMemory() {
      return true;
    }
  }
  Structure dup() {
    auto res = fastalloc!(Structure)(name);
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
    auto res = _size();
	// auto pre = res;
    doAlign(res, this);
    // if (res != pre) logln(pre, " -> "[], res, ": "[], this);
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
  RelMember[] members() { return selectMap!(RelMember, "$"[]); }
  Structure slice(int from, int to) {
    assert(!isUnion);
    auto res = fastalloc!(Structure)(cast(string) null);
    res.packed = packed;
    res.sup = sup;
    int i;
    select((string, RelMember member) { if (i !< from && i < to) fastalloc!(RelMember)(member.name, member.type, res); i++; }, &rmcache);
    return res;
  }
  NSCache!(string) namecache;
  NSCache!(IType) typecache;
  string[] names() { return selectMap!(RelMember, "$.name"[])(&namecache); }
  IType[] types() { return selectMap!(RelMember, "$.type"[])(&typecache); }
  int minAlign = 1; // minimal alignment for struct members (4 for C structs)
  this(string name) {
    this.name = name;
  }
  string manglecache;
  string mangle() {
    if (!manglecache) {
      string ersatzname = qformat("struct_"[], name.cleanup());
      if (!name) {
        ersatzname = "anon_struct";
        select((string, RelMember member) { ersatzname = qformat(ersatzname, "_", member.type.mangle, "_", member.name); }, &rmcache);
      }
      if (sup) manglecache = mangle(ersatzname, null);
      else manglecache = ersatzname;
    }
    return manglecache;
  }
  override {
    IType getRefType() { return fastalloc!(Pointer)(this); }
    string getIdentifier() { return name; }
    string mangle(string name, IType type) {
      string type_mangle;
      if (type) type_mangle = type.mangle() ~ "_";
      return sup.mangle(name, null)~"_"~type_mangle~name;
    }
    Stuple!(IType, string, int)[] stackframe() {
      return selectMap!(RelMember, "stuple($.type, $.name, $.offset)"[]);
    }
    Object lookupRel(string str, Expr base, bool isDirectLookup = true) {
      if (str == "tupleof") {
        return fastcast!(Object) (_make_tupleof(this, base));
      }
      auto res = lookup(str, true);
      if (auto rt = fastcast!(RelTransformable) (res))
        return fastcast!(Object) (rt.transform(base));
      return res;
    }
    // Let two structs be equal if their names and sizes are equal
    // and all their members are of the same size
    int opEquals(IType it) {
      auto str = fastcast!(Structure)~ it;
      if (!str) return false;
      if (str is this) return true;
      if (str.mangle() != mangle()) return false;
      if (str.size != size) return false;
      auto n1 = str.names(), n2 = names();
      if (n1.length != n2.length) return false;
      foreach (i, n; n1) if (n != n2[i]) return false;
      auto t1 = str.types(), t2 = types();
      foreach (i, v; t1) if (v.size != t2[i].size) return false;
      return true;
    }
    string toString() {
      if (!name) {
        string[] names;
        foreach (elem; field)
          if (auto n = fastcast!(Named) (elem._1)) {
            string id = n.getIdentifier();
            if (auto rm = fastcast!(RelMember) (elem._1))
              id = Format(id, "<"[], rm.valueType().size, ">@"[], rm.offset);
            names ~= id;
          }
        return Format("{struct "[], names.join(", "[]), "}"[]);
      }
      if (auto mn = get!(ModifiesName)) return mn.modify(name);
      return name;
    }
    bool isTempNamespace() { return isTempStruct; }
    void __add(string name, Object obj) {
      auto ex = fastcast!(Expr) (obj);
      if (ex && fastcast!(Variadic) (ex.valueType())) throw new Exception("Variadic tuple: Wtf is wrong with you. "[]);
      super.__add(name, obj);
    }
  }
}

import ast.modules;
bool matchStructBodySegment(ref string text, Namespace ns,
                     ParseCb* rest = null, bool alwaysReference = false, bool matchMany = true) {
  auto backup = namespace();
  namespace.set(ns);
  scope(exit) namespace.set(backup);
  
  Named smem;
  string t2;
  string[] names; IType[] types;
  string strname; IType strtype;
  
  Object match(ref string text, string rule) {
    if (rest) { Object res; if (!(*rest)(text, rule, &res)) return null; return res; }
    else {
      return parse(text, rule);
    }
  }
  
  bool expr() {
    auto backup = text;
    if (test(smem = fastcast!(Named)(match(text, "struct_member")))) {
      if (!addsSelf(smem)) ns.add(smem);
      return true;
    }
    text = backup;
    if (test(strtype = fastcast!(IType) (match(text, "type")))
      && text.bjoin(
        text.gotIdentifier(strname),
        text.accept(","[]),
        { names ~= strname; types ~= strtype; }
      ) && text.accept(";"[])) {
      foreach (i, strname; names)
        if (alwaysReference)
          fastalloc!(RelMemberLV)(strname, types[i], ns);
        else
          fastalloc!(RelMember)(strname, types[i], ns);
      names = null; types = null;
      return true;
    }
    text = backup;
    return false;
  }
  
  if (matchMany) return text.many(expr());
  else return expr();
}

// so templates can mark us as weak
class NoOpMangleHack : Statement, IsMangled {
  Structure sup;
  this(Structure s) { sup = s; }
  NoOpMangleHack dup() { return this; }
  override void emitLLVM(LLVMFile lf) { }
  mixin defaultIterate!();
  override string mangleSelf() { return sup.mangle(); }
  override void markWeak() {
    foreach (entry; sup.field)
      if (auto mg = fastcast!(IsMangled) (entry._1)) mg.markWeak();
  }
}

Object gotStructDef(bool returnIt)(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  bool isUnion;
  if (!t2.accept("struct"[])) {
    if (!t2.accept("union"[]))
      return null;
    isUnion = true;
  }
  string name;
  Structure st;
  if (t2.gotIdentifier(name) && t2.accept("{"[])) {
    New(st, name);
    st.isUnion = isUnion;
    
    auto ns = namespace();
    ns.add(st);
    while (fastcast!(Structure) (ns)) ns = ns.sup;
    st.sup = ns; // implicitly static
    
    auto rtptbackup = RefToParentType();
    scope(exit) RefToParentType.set(rtptbackup);
    RefToParentType.set(fastalloc!(Pointer)(st));
    
    auto rtpmbackup = *RefToParentModify();
    scope(exit) *RefToParentModify.ptr() = rtpmbackup;
    *RefToParentModify.ptr() = delegate Expr(Expr baseref) {
      return fastalloc!(DerefExpr)(baseref);
    };
    
    if (matchStructBodySegment(t2, st, &rest)) {
      if (!t2.accept("}"[]))
        t2.failparse("Missing closing struct bracket"[]);
      text = t2;
      static if (returnIt) return st;
      else return fastalloc!(NoOpMangleHack)(st);
    } else {
      t2.failparse("Couldn't match structure body"[]);
    }
  } else return null;
}
mixin DefaultParser!(gotStructDef!(false), "tree.typedef.struct"[]);
mixin DefaultParser!(gotStructDef!(false), "tree.stmt.typedef_struct"[], "32"[]);
mixin DefaultParser!(gotStructDef!(true), "struct_member.struct"[]);

class StructLiteral : Expr {
  Structure st;
  Expr[] exprs;
  int[] offsets;
  final void validate() {
    int offset = valueType().size;
    foreach_reverse (i, ex; exprs) {
      int wanted_pos = offsets[i];
      int emit_pos = wanted_pos + ex.valueType().size;
      if (emit_pos > offset) { logln(i, ": for ", st, ": ", emit_pos, " > ", offset, " (", offsets, "): ", exprs); fail; }
      offset = wanted_pos;
    }
  }
  this(Structure st, Expr[] exprs, int[] offsets) {
    if (exprs.length && !offsets.length) fail;
    this.st = st;
    foreach (ex; exprs) if (!ex) fail;
    this.offsets = offsets.dup;
    this.exprs = exprs.dup;
    validate();
  }
  private this() { }
  mixin defaultIterate!(exprs);
  override {
    string toString() { return Format("literal "[], st, " {"[], exprs, "}"[]); }
    StructLiteral dup() {
      auto res = new StructLiteral;
      res.st = st;
      res.offsets = offsets;
      res.exprs = exprs.dup;
      foreach (ref entry; res.exprs) entry = entry.dup;
      return res;
    }
    IType valueType() { return st; }
    void emitLLVM(LLVMFile lf) {
      validate();
      todo("StructLiteral::emitLLVM");
      /*mixin(mustOffset("st.size"[]));
      int offset = valueType().size;
      foreach_reverse (i, ex; exprs) {
        int wanted_pos = offsets[i];
        int emit_pos = wanted_pos + ex.valueType().size;
        if (emit_pos < offset) lf.salloc(offset - emit_pos);
        ex.emitLLVM(lf);
        offset = wanted_pos;
      }
      if (offset) lf.salloc(offset);*/
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
  /// intended as part of a set of accesses that will access every member of a struct.
  /// if true, we can optimize each individual access while assuming that side effects won't get lost.
  bool intendedForSplit;
  int counter;
  static int mae_counter;
  this() {
    counter = mae_counter ++;
    // if (counter == 2017) fail;
  }
  this(Expr base, string name) {
    this.base = base;
    this.name = name;
    this();
    auto ns = fastcast!(Namespace) (base.valueType());
    if (!ns) { logln("Base is not NS-typed: "[], base.valueType()); fail; }
    stm = fastcast!(RelMember) (ns.lookup(name));
    if (!stm) {
      logln("No member '"[], name, "' in "[], base.valueType(), "!"[]);
      fail;
    }
  }
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
      return qformat(counter, " ("[], base, "[])."[], name);
    }
    IType valueType() { return stm.type; }
    import tools.base;
    void emitLLVM(LLVMFile lf) {
      todo("MemberAccess_Expr::emitLLVM");
      /*auto st = base.valueType();
      if (auto lv = fastcast!(LValue)~ base) {
        if (stm.type.size <= 16) {
          lf.comment("emit location for member access to "[], stm.name, " @"[], stm.offset);
          lv.emitLocation(lf);
          lf.comment("pop and dereference"[]);
          if (isARM) {
            lf.popStack("r0"[], nativePtrSize);
            int sz = stm.type.size;
            if (sz == 2) {
              lf.salloc(2);
              lf.mmove2(qformat("[r0, #"[], stm.offset, "]"[]), "r1"[]);
              lf.mmove2("r1"[], "[sp]"[]);
            } else if (sz % 4 == 0) {
              for (int i = sz / 4 - 1; i >= 0; --i) {
                lf.mmove4(qformat("[r0, #"[], i * 4 + stm.offset, "]"[]), "r1"[]);
                lf.pushStack("r1"[], 4);
              }
            } else {
              logln(this, " with "[], stm);
              fail;
            }
          } else {
            lf.popStack("%eax"[], nativePtrSize);
            lf.comment("push back "[], stm.type.size);
            lf.pushStack(Format(stm.offset, "(%eax)"[]), stm.type.size);
            lf.nvm("%eax"[]);
          }
        } else {
          mkVar(lf, stm.type, true, (Variable var) {
            iparse!(Statement, "copy_struct_member"[], "tree.semicol_stmt.expr"[])
            ("memcpy(tempvarp, varp + offset, size)"[],
              "tempvarp"[], reinterpret_cast(voidp, fastalloc!(RefExpr)(var)),
              "varp"[], reinterpret_cast(voidp, fastalloc!(RefExpr)(lv)),
              "size"[], mkInt(stm.type.size),
              "offset"[], mkInt(stm.offset)
            ).emitLLVM(lf);
          });
        }
      } else {
        if (isARM) {
          base.emitLLVM(lf);
          if (stm.type.size == 4) {
            lf.mmove4(qformat("[sp, #"[], stm.offset, "]"[]), "r0"[]);
            lf.sfree(st.size);
            lf.pushStack("r0"[], 4);
            return;
          }
          if (stm.type.size == 8) {
            lf.mmove4(qformat("[sp, #"[], stm.offset, "]"[]), "r0"[]);
            lf.mmove4(qformat("[sp, #"[], stm.offset + 4, "]"[]), "r1"[]);
            lf.sfree(st.size);
            lf.pushStack("r1"[], 4);
            lf.pushStack("r0"[], 4);
            return;
          }
          logln("--"[], stm);
          fail;
        }
        // if (stm.type.size != 4) fail;
        // logln("full emit - worrying. "[], base, " SELECTING "[], stm);
        // fail;
        assert(stm.type.size == 1 /or/ 2 /or/ 4 /or/ 8 /or/ 12 /or/ 16, Format("Asked for "[], stm, " in "[], base.valueType(), "; bad size; cannot get "[], stm.type.size(), " from non-lvalue ("[], !fastcast!(LValue) (base), "[]) of "[], base.valueType().size(), ". "[]));
        auto bvt = base.valueType();
        lf.comment("emit semi-structure of "[], bvt, " for member access"[]);
        if (auto rce = fastcast!(RCE)~ base) bvt = rce.from.valueType();
        auto filler = alignStackFor(bvt, lf);
        base.emitLLVM(lf);
        lf.comment("store member and free: "[], stm.name);
        if (stm.type.size == 1)
          lf.mmove1(Format(stm.offset, "(%esp)"[]), "%dl"[]);
        if (stm.type.size == 2)
          lf.mmove2(Format(stm.offset, "(%esp)"[]), "%dx"[]);
        if (stm.type.size >= 4)
          lf.mmove4(Format(stm.offset, "(%esp)"[]), "%edx"[]);
        if (stm.type.size >= 8)
          lf.mmove4(Format(stm.offset + 4, "(%esp)"[]), "%ecx"[]);
        if (stm.type.size >= 12)
          lf.mmove4(Format(stm.offset + 8, "(%esp)"[]), "%eax"[]);
        if (stm.type.size == 16)
          lf.mmove4(Format(stm.offset + 12, "(%esp)"[]), "%ebx"[]);
        lf.sfree(st.size);
        lf.sfree(filler);
        lf.comment("repush member"[]);
        if (stm.type.size == 16) {
          lf.pushStack("%ebx"[], 4);
          lf.nvm("%ebx"[]);
        }
        if (stm.type.size >= 12) {
          lf.pushStack("%eax"[], 4);
          lf.nvm("%eax"[]);
        }
        if (stm.type.size >= 8) {
          lf.pushStack("%ecx"[], 4);
          lf.nvm("%ecx"[]);
        }
        if (stm.type.size >= 4) {
          lf.pushStack("%edx"[], 4);
          lf.nvm("%edx"[]);
        }
        if (stm.type.size == 2) {
          lf.pushStack("%dx"[], 2);
          lf.nvm("%dx"[]);
        }
        if (stm.type.size == 1) {
          lf.pushStack("%dl"[], 1);
          lf.nvm("%dl"[]);
        }
      }*/
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
    void emitLocation(LLVMFile lf) {
      todo("MemberAccess_LValue::emitLocation");
      /*auto st = fastcast!(Structure)~ base.valueType();
      int[] offs;
      if (st) offs = st.selectMap!(RelMember, "$.offset"[]);
      lf.comment("emit location for member address of '"[], stm.name, "' @"[], stm.offset, " of "[], offs);
      (fastcast!(LValue)~ base).emitLocation(lf);
      if (stm.offset) {
        lf.comment("add offset "[], stm.offset);
        if (isARM) {
          (fastalloc!(IntExpr)(stm.offset)).emitLLVM(lf);
          lf.popStack("r1"[], 4);
          lf.mmove4("[sp]"[], "r0"[]);
          // lf.mmove4(Format("#"[], stm.offset), "r1"[]);
          lf.mathOp("add"[], "r0"[], "r1"[], "r0"[]);
          lf.mmove4("r0"[], "[sp]"[]);
        } else {
          lf.mathOp("addl"[], Format("$"[], stm.offset), "(%esp)"[]);
        }
      }*/
    }
  }
}

import ast.fold, ast.casting;
static this() {
  foldopt ~= delegate Itr(Itr it) {
    if (auto r = fastcast!(RCE) (it)) {
      if (auto lit = fastcast!(StructLiteral)~ r.from) {
        if (lit.exprs.length == 1) {
          if (lit.exprs[0].valueType() == r.to)
            return fastcast!(Itr) (lit.exprs[0]); // pointless keeping a cast
          return reinterpret_cast(r.to, lit.exprs[0]);
        }
      }
    }
    return null;
  };
  foldopt ~= delegate Itr(Itr it) {
    if (auto mae = fastcast!(MemberAccess_Expr) (it)) {
      auto base = mae.base;
      auto basebackup = base;
      // logln(mae.name, "::"[], mae.stm.type.size, " vs. "[], base.valueType().size);
      if (mae.stm.type.size == base.valueType().size) {
        return fastcast!(Iterable) (foldex(reinterpret_cast(mae.stm.type, base)));
      }
      
      {
        Expr from;
        if (auto mae2 = fastcast!(MemberAccess_Expr)~ base) from = base; // lol direct
        if (auto c = fastcast!(RCL) (base)) from = c.from;
        if (auto c = fastcast!(RCE) (base)) from = c.from;
        if (from) {
          if (auto m2 = fastcast!(MemberAccess_Expr)~ from) {
            MemberAccess_Expr weird;
            if (fastcast!(MemberAccess_LValue) (from)) weird = new MemberAccess_LValue;
            else New(weird);
            weird.base = m2.base;
            weird.stm = fastalloc!(RelMember)(cast(string) null, mae.stm.type, mae.stm.offset + m2.stm.offset);
            return fastcast!(Iterable) (foldex(weird));
          }
        }
      }
      
      Structure st;
      if (auto rce = fastcast!(RCE)~ base) {
        base = rce.from;
        st = fastcast!(Structure)~ rce.to;
      }
      
      if (auto sl = fastcast!(StructLiteral)~ base) {
        if (!mae.intendedForSplit && sl.exprs.length > 1) {
          bool cheap = true;
          foreach (ref ex; sl.exprs) {
            // if it was for multiple access, it'd already have checked for that separately
            if (!_is_cheap(ex, CheapMode.Flatten)) {
              // logln("not cheap: "[], ex);
              cheap = false;
              break;
            }
          }
          if (!cheap) return null; // may be side effects of other expressions in the SL
        }
        Expr res;
        int i;
        if (!st)
          st = fastcast!(Structure)~ base.valueType();
        else {
          // TODO: assert: struct member offsets identical!
        }
        if (st) st.select((string, RelMember member) {
          if (member.type == mae.stm.type && member.offset == mae.stm.offset) {
            res = sl.exprs[i];
            // who cares!
            // if (mae.valueType() != res.valueType())
            //   logln("Type mismatch: "[], mae.valueType(), " vs. "[], res.valueType());
          }
          i++;
        }, &st.rmcache);
        if (auto it = fastcast!(Iterable) (res))
          return it;
      }
    }
    return null;
  };
  alignChecks ~= (IType it) {
    if (auto st = fastcast!(Structure) (it)) {
      return needsAlignmentStruct(st);
    }
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
      ex = fastalloc!(DerefExpr)(ex);
    } else break;
  }
  return ex;
}

extern(C) bool _isITemplate(Object obj);

import ast.parse, ast.fun, tools.base: or;
Object gotMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  assert(lhs_partial());
  auto first_ex = fastcast!(Expr)~ lhs_partial();
  auto t2 = text;
  string member;
  if (!t2.gotIdentifier(member)) return null;
  
  Expr ex;
  Expr[] alts;
  IType[] spaces;
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
      return false;
    });
    ex3 = ex;
    gotImplicitCast(ex3, (Expr ex) {
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
  
  auto backupmember = member;
  auto backupt2 = t2;
try_next_alt:
  member = backupmember; // retry from start again
  t2 = backupt2;
  if (!alts.length)
    return null;
  ex = alts[0]; alts = alts[1 .. $];
  auto space = spaces[0]; spaces = spaces[1 .. $];
  
  auto pre_ex = ex;
  
  auto rn = fastcast!(RelNamespace) (space);
retry:
  auto ns = fastcast!(Namespace) (space);
  if (!ex || !rn) {
    Object m;
    if (ns) m = ns.lookup(member, true);
    if (!m && rn) m = rn.lookupRel(member, null);
    if (!m) goto try_next_alt;
    
    // auto ex2 = fastcast!(Expr) (m);
    // if (!ex2) {
    // what
    /*if (!m) {
      if (t2.eatDash(member)) { logln("1 Reject "[], member, ": no match"[]); goto retry; }
      text.setError(Format("No "[], member, " in "[], ns, "!"[]));
      goto try_next_alt;
    }*/
    
    text = t2;
    return m;
  }
  auto m = rn.lookupRel(member, ex);
  if (!m) {
    if (t2.eatDash(member)) { goto retry; }
    string mesg, name;
    auto info = Format(pre_ex.valueType());
    if (info.length > 64) info = info[0..64] ~ " [snip]";
    if (auto st = fastcast!(Structure) (resolveType(fastcast!(IType) (rn)))) {
      name = st.name;
      /*logln("alts1 "[]);
      foreach (i, alt; alts)
        logln("  "[], i, ": "[], alt);*/
      mesg = Format(member, " is not a member of "[], pre_ex.valueType(), "[], containing "[], st.names);
    } else {
      /*logln("alts2: "[]);
      foreach (i, alt; alts)
        logln("  "[], i, ": "[], alt);*/
      mesg = Format(member, " is not a member of non-struct "[], info);
    }
    text.setError(mesg);
    goto try_next_alt;
  }
  text = t2;
  return m;
}
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_rel_member"[], null, "."[]);

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
    if (!t2.accept("."[])) return null;
    
    string id;
    if (!t2.gotIdentifier(id)) return null;
    retry:
      // logln("Try to "[], id, " into "[], ns);
      // logln(" => "[], ns.lookup(id), "[], left "[], t2.nextText());
      if (auto ty = fastcast!(IType) (ns.lookup(id))) {
        // logln("return "[], ty);
        text = t2;
        return ty;
      }
      if (t2.eatDash(id)) goto retry;
    return null;
  };
  implicits ~= delegate void(Expr ex, IType goal, void delegate(Expr) consider) {
    auto st = fastcast!(Structure) (ex.valueType());
    if (!st) return;
    for (int i = 1; true; i++) {
      if (auto res = fastcast!(Expr) (st.lookupRel("implicit-cast"~(i>1?Format("-"[], i):""[]), ex))) {
        // if (!goal || res.valueType() == goal) consider(res);
        consider(res);
      } else return;
    }
  };
  implicits ~= delegate void(Expr ex, IType goal, void delegate(Expr) consider) {
    auto st = fastcast!(Structure) (goal);
    if (!st) return;
    auto initval = reinterpret_cast(goal, fastalloc!(DataExpr)(goal.initval()));
    if (!showsAnySignOfHaving(initval, "init")) return;
    auto res = tmpize_maybe(initval, delegate Expr(Expr initval) {
      auto st = iparse!(Statement, "init_struct", "tree.stmt")
                       (`initval.init arg;`,
                        "initval", initval, "arg", ex);
      return mkStatementAndExpr(st, initval);
    });
    consider(res);
  };
}
