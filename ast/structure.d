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
  int index;
  string makeOffset(Structure base) {
    auto type = base.llvmType();
    return qformat("ptrtoint(", this.type.llvmType(), "* getelementptr(", type, "* null, i32 0, i32 ", index, ") to i32)");
  }
  override {
    string toString() { return Format("["[], name, ": "[], type, " @"[], index, "]"[]); }
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      logln("Untransformed rel member "[], this, ": cannot emit. "[]);
      fail;
    }
    mixin defaultIterate!();
    mixin defaultCollapse!();
    string getIdentifier() { return name; }
    Object transform(Expr base) {
      if (type.llvmSize() == base.valueType().llvmSize())
        return fastcast!(Object) (reinterpret_cast(type, base));
      return fastcast!(Object) (mkMemberAccess(base, name));
    }
  }
  this(string name, IType type, int index) {
    this.name = name;
    this.type = type;
    this.index = index;
  }
  this(string name, IType type, Namespace ns) {
    this(name, type, 0);
    auto sl = fastcast!(StructLike)~ ns;
    
    string stname;
    if (sl) {
      if (sl.immutableNow)
        throw new Exception(Format("Cannot add "[], this, " to "[], sl, ": size already fixed. "[]));
      index = sl.numMembers();
      stname = sl.getIdentifier();
    } else {
      todo(qformat("unno how to add rel member to ", ns));
    }
    
    // alignment
    bool isAligned = true;
    if (sl && sl.isPacked) isAligned = false;
    
    /*if (isAligned) {
      doAlign(offset, type);
      if (st && st.minAlign > 1) offset = roundTo(offset, st.minAlign);
    }*/
    // type may be incomplete, such as as_type(x) (int, x)*
    // if we require a type mangle here, we're forced to make up a name in ast.tuples
    // so, don't.
    if (!this.name) this.name = qformat("_anon_struct_member_"[], sl.numMembers()/*, "_of_"[], type.mangle()*/);
    ns.add(this);
  }
  override RelMember dup() { return this; }
}

class RelMemberLV : RelMember, LValue {
  void emitLocation(LLVMFile lf) {
    logln("Untransformed rel member "[], this, ": cannot emit location. "[]);
    fail;
  }
  RelMemberLV dup() { return new RelMemberLV(name, type, index); }
  this(string name, IType type, int index) { super(name, type, index); }
  this(string name, IType type, Namespace ns) { super(name, type, ns); }
}

extern(C) Expr _make_tupleof(Structure str, Expr ex);
extern(C) Expr _make_namesof(Structure str, Expr ex);
final class Structure : Namespace, RelNamespace, IType, Named, hasRefType, Importer, SelfAdding, StructLike, ExternAware {
  static const isFinal = true;
  mixin TypeDefaults!(false);
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
  bool isImmutableNow;
  int cached_length, cached_size;
  string cached_llvm_type, cached_llvm_size;
  string nameInfo() { return qformat(name, " in ", get!(IModule).getIdentifier()); }
  mixin ImporterImpl!();
  NSCache!(string, RelMember) rmcache;
  string offsetOfNext(IType it) {
    int len;
    string strtype;
    void append(string ty) {
      len ++;
      if (strtype) strtype ~= ", ";
      strtype ~= ty;
    }
    structDecompose(typeToLLVM(this), &append);
    auto thingy = typeToLLVM(it);
    append(thingy);
    strtype = "{"~strtype~"}";
    return lloffset(strtype, thingy, len-1);
  }
  void markExternC() {
    foreach (entry; field) {
      auto obj = entry._1;
      if (auto ex = fastcast!(Expr)(obj)) obj = fastcast!(Object)(ex.valueType());
      if (auto eat = fastcast!(ExternAware)(obj))
        eat.markExternC();
    }
  }
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
  bool immutableNow() { return isImmutableNow; }
  bool isPacked() { return packed; }
  string llvmType() {
    if (!cached_llvm_type) {
      if (isUnion) {
        auto sz = llvmSize();
        cached_llvm_type = qformat("[", sz, " x i8]");
      } else {
        string list;
        select((string, RelMember member) {
          if (list.length && member.index == 0) return; // freak of nature
          if (list.length) list ~= ", ";
          list ~= typeToLLVM(member.type, true);
        });
        cached_llvm_type = qformat("{", list, "}");
      }
    }
    return cached_llvm_type;
  }
  string llvmSize() {
    if (cached_llvm_size) return cached_llvm_size;
    {
      int num;
      string size;
      select((string, RelMember member) { num++; if (num == 1) size = member.type.llvmSize(); });
      if (num == 1) return size;
    }
    if (isUnion) {
      string len = "0";
      select((string, RelMember member) {
        len = llmax(len, member.type.llvmSize());
      });
      // logln("Structure::llvmSize for union ", this.name, " (oh noo): ", len.length);
      return len;
    }
    {
      int count;
      string size;
      bool sameSize = true;
      select((string, RelMember member) {
        auto msize = member.type.llvmSize();
        if (!sameSize || !size || msize != size) {
          if (!size) { size = msize; count = 1; }
          else {
            // hax
            if (member.name != "self") sameSize = false;
          }
        }
        else count++;
      });
      if (size && sameSize) {
        cached_llvm_size = llmul(qformat(count), size);
        return cached_llvm_size;
      }
    }
    auto ty = llvmType();
    cached_llvm_size = readllex(qformat("ptrtoint(", ty, "* getelementptr(", ty, "* null, i32 1) to i32)"));
    return cached_llvm_size;
  }
  Structure dup() {
    auto res = fastalloc!(Structure)(name);
    res.sup = sup;
    res.field = field.dup;
    res.rebuildCache();
    res.isUnion = isUnion; res.packed = packed; res.isTempStruct = isTempStruct;
    res.isImmutableNow = isImmutableNow;
    res.cached_length = cached_length; res.cached_size = cached_size;
    res.cached_llvm_type = cached_llvm_type;
    res.cached_llvm_size = cached_llvm_size;
    return res;
  }
  int numMembers() {
    int res;
    select((string, RelMember member) { res++; }, &rmcache);
    return res;
  }
  int length() {
    isImmutableNow = true;
    if (field.length == cached_length)
      if (cached_size) return cached_size;
    auto res = numMembers();
	// auto pre = res;
    // doAlign(res, this);
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
  IType getRefType() { return fastalloc!(Pointer)(this); }
  string getIdentifier() { return name; }
  string mangle(string name, IType type) {
    string type_mangle;
    if (type) type_mangle = type.mangle() ~ "_";
    return sup.mangle(name, null)~"_"~type_mangle~name;
  }
  Object lookupRel(string str, Expr base, bool isDirectLookup = true) {
    if (str == "tupleof") {
      return fastcast!(Object) (_make_tupleof(this, base));
    }
    if (str == "namesof") {
      return fastcast!(Object) (_make_namesof(this, base));
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
    if (str.length != length) return false;
    auto n1 = str.names(), n2 = names();
    if (n1.length != n2.length) return false;
    foreach (i, n; n1) if (n != n2[i]) return false;
    auto t1 = str.types(), t2 = types();
    foreach (i, v; t1) if (v.llvmType() != t2[i].llvmType()) return false;
    return true;
  }
  string toString() {
    if (!name) {
      string[] names;
      foreach (elem; field)
        if (auto n = fastcast!(Named) (elem._1)) {
          string id = n.getIdentifier();
          if (auto rm = fastcast!(RelMember) (elem._1))
            // id = Format(id, "<"[], rm.valueType().llvmType(), ">@"[], rm.index);
            id = Format(id, "<"[], rm.valueType(), ">@"[], rm.index);
          names ~= id;
        }
      return Format("{struct "[], names.join(", "[]), "}"[]);
    }
    if (auto mn = get!(ModifiesName)) return mn.modify(name);
    return name;
  }
  bool isTempNamespace() { return isTempStruct; }
  void __add(string name, Object obj) {
    cached_llvm_type = null;
    cached_llvm_size = null;
    auto ex = fastcast!(Expr) (obj);
    if (ex && fastcast!(Variadic) (ex.valueType())) throw new Exception("Variadic tuple: Wtf is wrong with you. "[]);
    super.__add(name, obj);
  }
}

import ast.modules;
bool matchStructBodySegment(ref string text, Namespace ns,
                     ParseCb* rest = null, bool alwaysReference = false, bool matchMany = true) {
  auto backup = namespace();
  namespace.set(ns);
  scope(exit) namespace.set(backup);
  
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
    Object obj;
    if (test(obj = match(text, "struct_member"))) {
      auto smem = fastcast!(Named)(obj);
      if (smem && !addsSelf(smem)) ns.add(smem);
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
        fastalloc!(RelMemberLV)(strname, types[i], ns);
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
  mixin defaultCollapse!();
  override string mangleSelf() { return sup.mangle(); }
  override void markWeak() {
    foreach (entry; sup.field)
      if (auto mg = fastcast!(IsMangled)(entry._1)) mg.markWeak();
  }
  override void markExternC() {
    sup.markExternC();
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
  bool safeToDiscard; // can throw away parts of this literal without running into issues
  this(Structure st, Expr[] exprs, bool std = false) {
    this.st = st;
    foreach (ex; exprs) if (!ex) fail;
    this.exprs = exprs.dup;
    this.safeToDiscard = std;
  }
  private this() { }
  mixin defaultIterate!(exprs);
  Expr collapse() {
    if (exprs.length == 1) {
      return reinterpret_cast(st, .collapse(exprs[0]));
    }
    return this;
  }
  override {
    string toString() { return Format("literal "[], st, " {"[], exprs, "}"[]); }
    StructLiteral dup() {
      auto res = new StructLiteral;
      res.st = st;
      res.safeToDiscard = safeToDiscard;
      res.exprs = exprs.dup;
      foreach (ref entry; res.exprs) entry = entry.dup;
      return res;
    }
    IType valueType() { return st; }
    void emitLLVM(LLVMFile lf) {
      auto parts = new string[exprs.length*2];
      // logln("slit ", exprs);
      // fill in reverse to conform with previous fcc's behavior
      foreach_reverse (i, ex; exprs) {
        auto ta = typeToLLVM(ex.valueType()), tb = typeToLLVM(ex.valueType(), true);
        if (ta == tb) {
          parts[i*2] = ta;
          parts[i*2+1] = save(lf, ex);
        } else {
          parts[i*2] = tb;
          llcast(lf, ta, tb, save(lf, ex));
          parts[i*2+1] = lf.pop();
        }
      }
      formTuple(lf, parts);
    }
  }
}

interface IRefTuple {
  MValue[] getMVs();
}

// ripped off from llcast in fcc.d
bool struct_types_with_same_layout(string a, string b) {
  if (!a.endsWith("}") || !b.endsWith("}")) return false; // not struct types
  string[] as, bs;
  structDecompose(a, (string s) { as ~= s; });
  structDecompose(b, (string s) { bs ~= s; });
  if (as.length != bs.length) return false;
  bool samelayout = true;
  foreach (i, t1; as) {
    auto t2 = bs[i];
    // if types are not (the same or both pointers)
    if (!(t1 == t2 || t1.endsWith("*") && t2.endsWith("*"))) {
      samelayout = false;
      break;
    }
  }
  return samelayout;
}

import ast.pointer;
class MemberAccess_Expr : Expr, HasInfo {
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
    // if (counter == 13255) fail;
  }
  this(Expr base, string name) {
    this.base = base;
    this.name = name;
    this();
    auto ns = fastcast!(Namespace) (base.valueType());
    if (!ns) { logln("Base is not NS-typed: "[], base.valueType(), " being ", base); fail; }
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
    res.stm = stm;
    res.name = name;
    return res;
  }
  mixin defaultIterate!(base);
  Expr collapse() {
    auto nbase = .collapse(base);
    auto lvnbase = fastcast!(LValue)(nbase);
    if (!fastcast!(MemberAccess_LValue)(this) && lvnbase) {
      if (!name) fail;
      auto res = fastalloc!(MemberAccess_LValue)();
      res.base = lvnbase.dup;
      res.stm = stm;
      res.name = name;
      return .collapse(fastcast!(Expr)(res));
    }
    bool deb;
    if (auto wte = fastcast!(WithTempExpr)(nbase)) {
      wte = fastcast!(WithTempExpr)(wte.dup);
      
      auto newmae = create();
      newmae.base = wte.superthing;
      newmae.stm  = stm;
      newmae.name = name;
      
      wte.superthing = .collapse(fastcast!(Expr)(newmae));
      return wte;
    }
    /*if (stm.name == "fun") {
      deb = true;
    }*/
    if (deb) logln("deb on");
    if (stm.type.llvmType() == base.valueType().llvmType()) {
      if (deb) logln("deb early direct-match for ", this, " => ", base);
      return reinterpret_cast(stm.type, base);
    }
    
    Structure st;
    if (auto rce = fastcast!(RCE)~ nbase) {
      nbase = .collapse(rce.from);
      st = fastcast!(Structure) (resolveType(rce.to));
    }
    
    if (nbase.valueType() == stm.type) {
      if (deb) logln("deb direct-match for ", this, " => ", nbase);
      return nbase;
    }
    if (st && st.length == 1) {
      if (deb) logln("deb foldopt cast ", st, " TO ", stm.type);
      return reinterpret_cast(stm.type, nbase);
    }
    {
      if (deb) {
        logln("deb bvt = ", nbase.valueType());
        logln("being ", nbase.valueType().llvmSize());
        logln("  and ", stm.type.llvmSize());
      }
      auto sx = fastcast!(Structure)(nbase.valueType());
      if (sx && sx.llvmSize() == stm.type.llvmSize()) { // close enough
        return reinterpret_cast(stm.type, nbase);
      }
    }
    if (deb) {
      logln("deb with ", stm, " into ", st);
      logln("deb BASE = ", fastcast!(Object)(nbase).classinfo.name, " ", nbase);
    }
    if (auto sl = fastcast!(StructLiteral) (nbase)) {
      if (deb) {
        foreach (expr; sl.exprs) {
          logln("  ", expr);
        }
      }
      if (!intendedForSplit && !sl.safeToDiscard && sl.exprs.length > 1) {
        bool cheap = true;
        foreach (ref ex; sl.exprs) {
          // if it was for multiple access, it'd already have checked for that separately
          if (!_is_cheap(ex, CheapMode.Flatten)) {
            if (deb) logln("not cheap: "[], ex);
            cheap = false;
            break;
          }
        }
        if (!cheap) return this; // may be side effects of other expressions in the SL
      }
      Expr res;
      int i;
      if (!st)
        st = fastcast!(Structure) (resolveType(base.valueType()));
      else {
        // TODO: assert: struct member offsets identical!
      }
      if (st && struct_types_with_same_layout(typeToLLVM(st), typeToLLVM(sl.valueType()))) st.select((string, RelMember member) {
        if (member.index == stm.index) {
          res = .collapse(reinterpret_cast(stm.valueType(), sl.exprs[i]));
        }
        i++;
      }, &st.rmcache);
      if (deb) {
        logln(" => ", res);
        logln("(st ", st, ")");
      }
      if (auto tr = fastcast!(Tree) (res))
        return tr;
    }
    
    if (auto rt = fastcast!(IRefTuple)(nbase)) {
      if (!st) {
        logln("what? ", nbase, " but! ", resolveType(base.valueType()));
        fail;
      }
      auto members = st.members();
    retry:
      auto mvs = rt.getMVs();
      if (members.length > 1 && mvs.length == 1) {
        rt = fastcast!(IRefTuple) (.collapse(fastcast!(Expr)(mvs[0])));
        if (rt) goto retry;
        else return this; // TODO: I don't get this. 
      }
      if (!rt || mvs.length != members.length) {
        // this can happen if we're in a situation where
        // we're casting a reftuple to a completely different type
        // like (delegate, something) to (void*, void*, void*)
        // but! if this can happen, doesn't mean that this optimization is fundamentally flawed?
        // NOPE, because we is-compare entry and stm.
        return this;
        logln("ref tuple not large enough for this cast! ");
        logln(rt, " but ", members);
        fail;
      }
      int offs = -1;
      foreach (id, entry; members) if (entry is stm) { offs = id; break; }
      if (offs == -1) {
        // this can happen, for instance, if we
        // (erroneously!) collapsed two maes, one of which 
        // was larger -
        // for example, (a, (b, c)) accessing 'b' won't be found in the outer tuple
        fail;
      }
      return fastcast!(Tree) (mvs[offs]);
    }
    
    return this;
  }
  override {
    import tools.log;
    string toString() {
      return qformat(counter, " ("[], base, ")."[], name);
    }
    IType valueType() { return stm.type; }
    import tools.base;
    void emitLLVM(LLVMFile lf) {
      auto bvt = resolveType(base.valueType());
      auto bs = typeToLLVM(bvt);
      string src, srctype, extype;
      if (auto rce = fastcast!(RCE)(base)) {
        auto rfv = typeToLLVM(rce.from.valueType());
        if (struct_types_with_same_layout(bs, rfv)) {
          // logln("fold rce into mae: ", bs, " and ", rfv);
          src = save(lf, rce.from);
          srctype = rfv;
          string[] strl;
          structDecompose(rfv, (string s) { strl ~= s; });
          extype = strl[stm.index];
        }/* else {
          logln("different layouts: ", bs, " and ", rfv);
        }*/
      }
      if (!src) {
        src = save(lf, base);
        srctype = typeToLLVM(bvt);
        extype = typeToLLVM(stm.type, true);
      }
      // logln("1 bvt for ", this, " = ", fastcast!(Object)(bvt).classinfo.name, " ", bvt);
      if (fastcast!(Structure)(bvt).isUnion) {
        auto mt = typeToLLVM(stm.type);
        auto tmp = alloca(lf, "1", bs);
        put(lf, "; of union");
        put(lf, "store ", bs, " ", src, ", ", bs, "* ", tmp);
        load(lf, "load ", mt, "* ", bitcastptr(lf, bs, mt, tmp));
        return;
      }
      // put(lf, "; mae ", this);
      // put(lf, "; to ", stm, " into ", typeToLLVM(bvt), " (", bvt, ")");
      // don't want to fall over and die if user code has a variable called "self"
      // if (name == "self") fail; // ast.vector done a baad baad thing
      auto ex = save(lf, "extractvalue ", srctype, " ", src, ", ", stm.index);
      auto from = extype, to = typeToLLVM(stm.type);
      if (from == to) { push(lf, ex); }
      else { llcast(lf, from, to, ex); }
    }
  }
}

class MemberAccess_LValue_ : MemberAccess_Expr, LValue {
  int id;
  this(LValue base, string name) {
    super(fastcast!(Expr)~ base, name);
  }
  this() { }
  override {
    MemberAccess_LValue_ create() { return new MemberAccess_LValue_; }
    MemberAccess_LValue_ dup() { return fastcast!(MemberAccess_LValue_) (super.dup()); }
    void emitLLVM(LLVMFile lf) {
      emitLocation(lf);
      auto ls = lf.pop();
      auto lt = typeToLLVM(stm.type)~"*";
      load(lf, "load ", lt, " ", ls);
    }
    void emitLocation(LLVMFile lf) {
      (fastcast!(LValue)(base)).emitLocation(lf);
      auto ls = lf.pop();
      auto bvt = resolveType(base.valueType());
      // logln("2 bvt for ", this, " = ", fastcast!(Object)(bvt).classinfo.name, " ", bvt);
      if (fastcast!(Structure)(bvt).isUnion) {
        auto mt = typeToLLVM(stm.type);
        push(lf, bitcastptr(lf, typeToLLVM(bvt), mt, ls));
        return;
      }
      load(lf, "getelementptr inbounds ", typeToLLVM(bvt), "* ", ls, ", i32 0, i32 ", stm.index);
      auto restype = stm.type;
      auto from = typeToLLVM(restype, true)~"*", to = typeToLLVM(restype)~"*";
      // logln(lf.count, ": emitLocation of mal to ", bvt, ", from ", from, ", to ", to);
      if (from != to) {
        llcast(lf, from, to, lf.pop(), qformat(nativePtrSize));
      }
    }
  }
}

final class MemberAccess_LValue : MemberAccess_LValue_ {
  static const isFinal = true;
  MemberAccess_LValue create() { return new MemberAccess_LValue; }
  this(LValue base, string name) { super(base, name); }
  this() { super(); }
}

import ast.fold, ast.casting;
static this() {
  alignChecks ~= (IType it) {
    if (auto st = fastcast!(Structure) (it)) {
      return needsAlignmentStruct(st);
    }
    return 0;
  };
}

Expr mkMemberAccess(Expr strct, string name) {
  if(auto lv=fastcast!(LValue)(strct)) return fastalloc!(MemberAccess_LValue)(lv, name);
  else                                 return fastalloc!(MemberAccess_Expr  )(strct, name);
}

pragma(set_attribute, C_mkMemberAccess, externally_visible);
extern(C) Expr C_mkMemberAccess(Expr strct, string name) { return mkMemberAccess(strct, name); }

Expr[] splitStruct(Expr ex) {
  auto st = fastcast!(Structure)(resolveType(ex.valueType()));
  if (!st) fail;
  
  auto types = st.types();
  Expr[] res;
  foreach (i, type; types) {
    MemberAccess_Expr mae;
    if (fastcast!(LValue) (ex)) mae = fastalloc!(MemberAccess_LValue)();
    else mae = fastalloc!(MemberAccess_Expr)();
    
    mae.base = ex;
    mae.intendedForSplit = true;
    mae.name = qformat("_"[], i);
    
    auto mbrs = st.selectMap!(RelMember, "$"[]);
    if (i >= mbrs.length) fail;
    mae.stm = mbrs[i];
    res ~= mae;
  }
  return res;
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
  
  Expr[] alts;
  IType[] spaces;
  int[] scores;
  if (first_ex) {
    Expr ex = first_ex;
    auto ex3 = ex;
    Expr[] cleanups;
    int score;
    gotImplicitCast(ex3, (Expr ex) {
      auto vt = ex.valueType();
      if (auto srn = fastcast!(SemiRelNamespace) (vt))
        vt = fastcast!(IType) (srn.resolve());
      if (auto rn = fastcast!(RelNamespace) (vt)) {
        own_append(alts, ex);
        own_append(spaces, vt);
        own_append(scores, score);
      } else own_append(cleanups, ex);
      return false;
    }, false, &score);
    foreach (c; cleanups) cleanupex(c, true);
    cleanups = null;
    
    ex3 = ex;
    gotImplicitCast(ex3, (Expr ex) {
      auto ex4 = depointer(ex);
      if (ex4 !is ex) {
        gotImplicitCast(ex4, (Expr ex) {
          auto vt = ex.valueType();
          if (auto srn = fastcast!(SemiRelNamespace) (vt))
            vt = fastcast!(IType) (srn.resolve());
          if (auto rn = fastcast!(RelNamespace) (vt)) {
            own_append(alts, ex);
            own_append(spaces, vt);
            own_append(scores, score);
          } else own_append(cleanups, ex);
          return false;
        }, false, &score);
      } else own_append(cleanups, ex);
      return false;
    }, false);
    foreach (c; cleanups) cleanupex(c, true);
    cleanups = null;
    
  } else {
    if (auto ty = fastcast!(IType) (lhs_partial())) {
      auto vt = resolveType(ty);
      if (auto srn = fastcast!(SemiRelNamespace) (vt))
        vt = fastcast!(IType) (srn.resolve());
      
      if (fastcast!(Namespace) (vt) || fastcast!(RelNamespace) (vt)) {
        own_append(alts, cast(Expr) null);
        own_append(spaces, vt);
        own_append(scores, 0);
      }
    }
  }
  if (!alts.length) {
    return null;
  }
  
  // insertion sort by scores
  for (int cur = 1; cur < scores.length - 1; cur ++) {
    auto myalt = alts[cur], myspace = spaces[cur], myscore = scores[cur];
    int backwards = cur - 1;
    while (backwards >= 0 && scores[backwards] > myscore) {
      // shift backwards to the right to make space
      alts[backwards+1] = alts[backwards];
      spaces[backwards+1] = spaces[backwards];
      scores[backwards+1] = scores[backwards];
      backwards --;
    }
    // insert
    if (backwards+1 < cur) {
      alts[backwards+1] = myalt;
      spaces[backwards+1] = myspace;
      scores[backwards+1] = myscore;
    }
  }
  
  auto backupmember = member;
  auto backupt2 = t2;
  Expr ex;
  string mesg;
try_next_alt:
  member = backupmember; // retry from start again
  t2 = backupt2;
  if (!alts.length) {
    if (!(member in reservedPropertyNames))
      text.setError(mesg);
    return null;
  }
  
  // logln("try ", alts[0], " from ", alts, " ", scores);
  // logln(":: ", spaces[0]);
  // scope(exit) logln(":: exit");
  
  if (ex) if (auto tmp = fastcast!(Temporary)(ex)) tmp.cleanup(true);
  
  ex = alts[0]; alts = alts[1 .. $];
  auto space = spaces[0]; spaces = spaces[1 .. $];
  scores = scores[1 .. $];
  
  auto pre_ex = ex;
  
  auto rn = fastcast!(RelNamespace) (space);
retry:
  auto ns = fastcast!(Namespace) (space);
  if (!ex || !rn) {
    Object m;
    try {
      if (ns) m = ns.lookup(member, true);
      if (!m && rn) m = rn.lookupRel(member, null);
    } catch (Exception ex) {
      text.failparse(ex);
    }
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
  Object m;
  try m = rn.lookupRel(member, ex);
  catch (Exception ex) {
    text.failparse(ex);
  }
  // logln("::: ", m, " ", (fastcast!(Expr)(m))?(fastcast!(Expr)(m)).valueType():null);
  if (!m) {
    if (t2.eatDash(member)) { goto retry; }
    auto info = Format(pre_ex.valueType());
    if (info.length > 64) info = info[0..64] ~ " [snip]";
    if (auto st = fastcast!(Structure) (resolveType(fastcast!(IType) (rn)))) {
      // name = st.name;
      /*logln("alts1 "[]);
      foreach (i, alt; alts)
        logln("  "[], i, ": "[], alt);*/
      mesg = qformat(member, " is not a member of "[], info, ", containing "[], st.names);
    } else {
      /*logln("alts2: "[]);
      foreach (i, alt; alts)
        logln("  "[], i, ": "[], alt);*/
      mesg = qformat(member, " is not a member of non-struct "[], info);
    }
    // text.setError(mesg);
    goto try_next_alt;
  }
  text = t2;
  return m;
}
mixin DefaultParser!(gotMemberExpr, "tree.rhs_partial.access_rel_member"[], null, "."[]);
