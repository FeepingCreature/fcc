module ast.oop;

import ast.parse, ast.base, ast.dg, ast.int_literal, ast.fun,
  ast.namespace, ast.structure, ast.structfuns, ast.pointer,
  ast.arrays, ast.aggregate, ast.literals, ast.slice, ast.nestfun,
  ast.tenth;

struct RelFunSet {
  Stuple!(RelFunction, string, IType[])[] set;
  string toString() {
    return Format(set /map/ ex!("a, b, c -> b"));
  }
  RelFunction[] lookup(string name) {
    RelFunction[] res;
    foreach (entry; set)
      if (entry._1 == name) res ~= entry._0;
    return res;
  }
  static bool IType_eq(IType[] a, IType[] b) {
    if (a.length != b.length) return false;
    foreach (i, v; a) if (v != b[i]) return false;
    return true;
  }
  RelFunction lookup(string st, IType[] types) {
    foreach (entry; set) {
      if (entry._1 == st && IType_eq(entry._2, types))
        return entry._0;
    }
    return null;
  }
  RelFunction hasLike(Function f) {
    return lookup(f.name, f.type.types());
  }
  void add(string name, RelFunction rf) {
    set ~= stuple(rf, name, rf.type.types());
  }
  // append to set those of rfs.set _not_ yet in set
  void fillIn(RelFunSet rfs) {
    foreach (entry; rfs.set) {
      if (!lookup(entry._1, entry._2))
        set ~= entry;
    }
  }
}

import tools.log, tools.compat: max;
import ast.vardecl;
class VTable {
  RelFunction[] funs;
  Class parent;
  static bool Arglist_eq(Argument[] a, Argument[] b) {
    if (a.length != b.length) return false;
    foreach (i, v; a) if (v.type != b[i].type) return false;
    return true;
  }
  bool defines(Function fun) {
    foreach (f2; funs) {
      if (f2.name == fun.name &&
          Arglist_eq(f2.getParams(), fun.getParams())) return true;
    }
    return false;
  }
  Object lookup(string name, Expr classref) {
    int base = (parent.parent?parent.parent.getClassinfo().length:0);
    Function[] res;
    foreach (id, fun; funs)
      if (fun.name == name) {
        if (!classref) return fun;
        Statement initSt;
        Expr classref2 = lvize(classref, &initSt);
        res ~= 
          new PointerFunction!(NestedFunction) (
            new DgConstructExpr(
              new DerefExpr(
                lookupOp("+",
                  new DerefExpr(
                    reinterpret_cast(
                      new Pointer(new Pointer(fun.typeAsFp())),
                      classref2)),
                  mkInt(id+base))),
              reinterpret_cast(voidp, classref2)),
            initSt
          );
      }
    // logln(parent.name, ": ", name, " => ", res);
    if (res.length == 1) return fastcast!(Object) (res[0]);
    if (res.length == 0) return null;
    return new OverloadSet(res[0].name, res);
  }
  Object lookupFinal(string name, Expr classref) {
    auto classval = new DerefExpr(reinterpret_cast(voidpp, classref));
    Function[] res;
    if (auto list = parent.overrides.lookup(name))
      res ~= list;
    // return fastcast!(Function) (fastcast!(RelFunction) (*p).transform(classval));
    foreach (fun; funs)
      if (fun.name == name)
        res ~= fun;
    foreach (ref entry; res)
      entry = fastcast!(Function) (
        fastcast!(RelFunction) (entry).transform(classval)
      );
    if (res.length == 1) return fastcast!(Object) (res[0]);
    if (res.length == 0) return null;
    return new OverloadSet(res[0].name, res);
  }
}

// lookupRel in interfaces/classes takes the class *reference*.
// This is IMPORTANT for compat with using.

class Intf : IType, Tree, RelNamespace, IsMangled {
  string name;
  bool predecl;
  mixin TypeDefaults!();
  override int size() { assert(false); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override void emitAsm(AsmFile af) { }
  override bool isTempNamespace() { return false; }
  override bool isPointerLess() { return false; }
  override bool isComplete() { return true; }
  IntfRef getRefType() { return new IntfRef(this); }
  string toString() { return "interface "~name; }
  string mangle() { return "interface_"~mangle_id; }
  bool weak;
  override void markWeak() { weak = true; }
  override string mangleSelf() { return mangle(); }
  Function[] funs;
  Intf[] parents;
  string mangle_id;
  this(string name) {
    this.name = name;
    mangle_id = namespace().mangle(name, this);
  }
  bool declares(string name) {
    foreach (fun; funs) if (fun.name == name) return true;
    foreach (par; parents) if (par.declares(name)) return true;
    return false;
  }
  int clsize() {
    int res;
    if (!parents.length) res = 1;
    else {
      res = parents[0].clsize();
      foreach (par; parents[1 .. $])
        res += par.clsize();
    }
    return res + funs.length;
  }
  int own_offset;
  void initOffset() { own_offset = clsize() - funs.length; }
  // offset is size of preceding data, in steps of nativePtrSize
  string[] genClassinfo(ref int offset, RelFunSet overrides) {
    string[] res;
    if (!parents.length)
      res ~= Format("-", offset++);
    else {
      res = parents[0].genClassinfo(offset, overrides);
      foreach (par; parents[1 .. $])
        res ~= par.genClassinfo(offset, overrides);
    }
    
    foreach (fun; funs)
      if (auto rel = overrides.hasLike(fun))
        res ~= rel.mangleSelf();
      else
        throw new Exception(
          Format("Cannot generate classinfo for ", this.name,
            ": ", fun.name, " not overridden. "));
    
    return res;
  }
  import ast.index;
  Function lookupIntf(string name, Expr intp, Statement initSt = null) {
    assert(own_offset);
    foreach (id, fun; funs) {
      if (fun.name == name) {
        if (!intp) return fun;
        auto fntype = fun.getPointer().valueType();
        auto pp_fntype = new Pointer(new Pointer(fntype));
        auto pp_int = Single!(Pointer, Single!(Pointer, Single!(SysInt)));
        // *(*fntype**:intp)[id].toDg(void**:intp + **int**:intp)
        return new PointerFunction!(NestedFunction) (
          new DgConstructExpr(
            new PA_Access(new DerefExpr(reinterpret_cast(pp_fntype, intp)), mkInt(id + own_offset)),
            lookupOp("+",
              reinterpret_cast(new Pointer(voidp), intp),
              new DerefExpr(new DerefExpr(reinterpret_cast(pp_int, intp)))
            )
          ),
          initSt
        );
      }
    }
    return null;
  }
  override Object lookupRel(string name, Expr base) {
    if (!base) {
      if (name == "__name") // T.name
        return fastcast!(Object) (mkString(this.name));
      return lookupIntf(name, null);
    }
    if (!fastcast!(IntfRef) (base.valueType())) {
      logln("Bad intf ref: ", base);
      fail;
    }
    if (name == "this") return fastcast!(Object)~ base;
    // haaaaax
    Statement initSt;
    if (!namespace().get!(MiniNamespace))
      base = lvize(base, &initSt);
    auto cv = fastcast!(CValue)~ base;
    if (!cv) {
      // logln("intf lookupRel fail ", base, " '", (cast(Object) base).classinfo.name, "'");
      return null;
    }
    // auto self = new RefExpr(cv);
    auto self = cv;
    return lookupIntf(name, self, initSt);
  }
  Function lookupClass(string name, Expr offs, Expr classref) {
    assert(own_offset, this.name~": interface lookup for "~name~" but classinfo uninitialized. ");
    foreach (id, fun; funs) {
      if (fun.name == name) {
        // *(*fntype**:classref)[id + offs].toDg(void*:classref)
        auto fntype = fun.getPointer().valueType();
        auto pp_fntype = new Pointer(new Pointer(fntype));
        return new PointerFunction!(NestedFunction)(
          new DgConstructExpr(
            new PA_Access(new DerefExpr(reinterpret_cast(pp_fntype, classref)), lookupOp("+", offs, mkInt(id + own_offset))),
            reinterpret_cast(voidp, classref)
          )
        );
      }
    }
    foreach (par; parents) {
      if (auto res = par.lookupClass(name, offs, classref)) return res;
      offs = foldex(lookupOp("+", offs, mkInt(par.clsize)));
    }
    return null;
  }
  void getLeaves(void delegate(Intf) dg) {
    if (!parents.length) dg(this);
    else foreach (parent; parents) parent.getLeaves(dg);
  }
}

class ClassRef : Type, SemiRelNamespace, Formatable, Tree, Named, SelfAdding, IsMangled, ExprLikeThingy {
  Class myClass;
  this(Class cl) { myClass = cl; if (!cl) fail; }
  override {
    bool isPointerLess() { return false; }
    RelNamespace resolve() { return myClass; }
    string toString() { return Format("ref ", myClass); }
    bool addsSelf() { return true; }
    string getIdentifier() { return myClass.name; }
    int size() { return nativePtrSize; }
    void markWeak() { myClass.markWeak(); }
    string mangle() { return "ref_"~myClass.mangle(); }
    string mangleSelf() { return mangle(); }
    int opEquals(IType type) {
      if (!super.opEquals(type)) return false;
      // logln("test ", type, " against ", this);
      return myClass == (fastcast!(ClassRef) (resolveType(type))).myClass;
    }
    Expr format(Expr ex) {
      return iparse!(Expr, "gen_obj_toString_call_again_o_o", "tree.expr")
                    (`obj.toString()`, "obj", lvize(ex));
    }
    ClassRef dup() { return new ClassRef(myClass.dup); }
    void emitAsm(AsmFile af) { myClass.emitAsm(af); }
    void iterate(void delegate(ref Iterable) dg) { myClass.iterate(dg); }
  }
}

class IntfRef : Type, SemiRelNamespace, Tree, Named, SelfAdding, IsMangled, ExprLikeThingy {
  Intf myIntf;
  this(Intf i) { myIntf = i; }
  override {
    RelNamespace resolve() { return myIntf; }
    string toString() { return Format("ref ", myIntf); }
    string getIdentifier() { return myIntf.name; }
    bool isPointerLess() { return false; }
    bool addsSelf() { return true; }
    int size() { return nativePtrSize; }
    void markWeak() { } // nothing emitted, ergo no-op
    string mangle() { return "intfref_"~myIntf.mangle(); }
    string mangleSelf() { return mangle(); }
    int opEquals(IType type) {
      if (!super.opEquals(type)) return false;
      return myIntf is (fastcast!(IntfRef) (resolveType(type))).myIntf;
    }
    IntfRef dup() { return new IntfRef(myIntf.dup); }
    void emitAsm(AsmFile af) { myIntf.emitAsm(af); }
    void iterate(void delegate(ref Iterable) dg) { myIntf.iterate(dg); }
  }
}

class SuperType : IType, RelNamespace {
  ClassRef baseType;
  this(ClassRef cr) { baseType = cr; }
  override {
    int size() { return baseType.size(); }
    string toString() { return Format(baseType, ".super (", baseType.myClass.parent.myfuns.funs, ")"); }
    string mangle() { return Format("_super_", baseType.mangle()); }
    ubyte[] initval() { logln("Excuse me what are you doing declaring variables of super-type you weirdo"); fail; return null; }
    int opEquals(IType it) { return false; /* wut */ }
    bool isPointerLess() { return false; }
    override bool isComplete() { return true; }
    Object lookupRel(string name, Expr base) {
      auto sup2 = fastcast!(SuperType) (base.valueType());
      if (sup2 !is this) fail;
      // iterate parents
      Class parent_class = baseType.myClass.parent;
      while (parent_class) {
        auto suptable = parent_class.myfuns;
        if (auto res = suptable.lookupFinal(name, reinterpret_cast(parent_class.getRefType, base)))
          return res;
        parent_class = parent_class.parent;
      }
      return null;
    }
    bool isTempNamespace() { return true; }
    IType proxyType() { return null; }
  }
}

import ast.modules, ast.returns, ast.scopes, ast.stringparse;
class Class : Namespace, RelNamespace, IType, Tree, hasRefType {
  VTable myfuns;
  Structure data;
  string name;
  Class parent;
  Intf[] iparents;
  RelMember ctx; // context of parent reference
  Expr delegate(Expr) ctxFixup;
  
  string coarseSrc;
  Namespace coarseCtx;
  void parseMe() {
    if (!coarseSrc || !coarseCtx) return;
    
    auto backup = namespace();
    scope(exit) namespace.set(backup);
    namespace.set(coarseCtx);
    coarseCtx = null;
    
    pushCache();
    scope(exit) popCache();
    
    string t2 = coarseSrc;
    coarseSrc = null;
    
    auto classref = fastcast!(ClassRef) (getRefType());
    
    auto rtptbackup = RefToParentType();
    scope(exit) RefToParentType.set(rtptbackup);
    RefToParentType.set(classref);
    
    auto rtpmbackup = *RefToParentModify();
    scope(exit) *RefToParentModify.ptr() = rtpmbackup;
    *RefToParentModify.ptr() = delegate Expr(Expr baseref) { return baseref; /* no-op, classes are already ref */ };
    
    if (!t2.accept("{")) t2.failparse("Missing opening bracket for class def");
    
    if (matchStructBody(t2, this)) {
      if (!t2.accept("}"))
        t2.failparse("Failed to parse class body");
      // logln("register class ", cl.name);
      try finalize;
      catch (Exception ex) t2.failparse(ex);
      coarseSrc = null;
      coarseCtx = null;
      return;
    } else {
      t2.failparse("Couldn't match class body");
    }
  }
  
  string toString() { return Format("class ", name, " <- ", sup); }
  override int opEquals(Object obj2) {
    if (this is obj2) return true;
    auto cl2 = fastcast!(Class) (obj2);
    if (!cl2) return false;
    return mangle() == cl2.mangle();
  }
  override bool isPointerLess() { return false; }
  override bool isComplete() { return true; }
  void getIntfLeaves(void delegate(Intf) dg) {
    parseMe;
    foreach (intf; iparents)
      intf.getLeaves(dg);
  }
  RelFunSet overrides;
  string mangle_id;
  bool weak;
  void markWeak() { parseMe; weak = true; foreach (fun; myfuns.funs) (fastcast!(IsMangled) (fun)).markWeak(); }
  override string mangle() { return mangle_id; }
  override Class dup() { return this; }
  bool isTempNamespace() { return false; }
  this(string name, Class parent) {
    mangle_id = namespace().mangle(name, null);
    auto root = fastcast!(ClassRef)  (sysmod?sysmod.lookup("Object"):null);
    if (root) {
      if (name == "Object")
        throw new Exception("Can't redefine Object! ");
    } else {
      if (name != "Object")
        throw new Exception("Object must be first class defined! ");
    }
    if (!parent) parent = root?root.myClass:null;
    this.name = name;
    New(myfuns);
    myfuns.parent = this;
    this.parent = parent;
    if (!parent) {
      New(data, cast(string) null);
      new RelMember("classinfo", voidp, data);
    } else {
      parent.parseMe;
      data = parent.data.dup();
    }
    if (auto it = RefToParentType()) {
      ctx = new RelMember("context", it, this);
      ctxFixup = *RefToParentModify.ptr();
    }
    sup = namespace();
    if (namespace() !is current_module()) {
      current_module().entries ~= this;
    }
  }
  bool finalized;
  void genDefaultFuns() {
    if (sysmod && parent /* exclude Object */) {
      bool hasToStringOverride = !!overrides.lookup("toString", null);
      auto cur = this;
      while (cur.parent) {
        auto tsv = fastcast!(RelFunction) (cur.overrides.lookup("toString", null));
        hasToStringOverride |= tsv && !tsv.autogenerated;
        cur = cur.parent;
      }
      if (!hasToStringOverride) {
        auto rf = new RelFunction(this);
        New(rf.type);
        rf.name = "toString";
        rf.type.ret = Single!(Array, Single!(Char));
        rf.sup = this;
        rf.fixup;
        rf.autogenerated = true;
        (fastcast!(IsMangled) (rf)).markWeak();
        _add("toString", rf);
        auto backup = namespace();
        namespace.set(rf);
        scope(exit) namespace.set(backup);
        auto sc = new Scope;
        namespace.set(sc);
        rf.tree = sc;
        sc._body = new ReturnStmt(mkString(name));
        current_module().entries ~= rf;
      }
    }
    {
      auto rf = new RelFunction(this);
      New(rf.type);
      rf.name = "dynamicCastTo";
      rf.type.ret = voidp;
      rf.type.params ~= Argument(Single!(Array, Single!(Char)), "id");
      rf.sup = this;
      rf.fixup;
      (fastcast!(IsMangled) (rf)).markWeak();
      add(rf);
      auto backup = namespace();
      namespace.set(rf);
      scope(exit) namespace.set(backup);
      auto sc = new Scope;
      namespace.set(sc);
      // TODO: switch
      auto as = new AggrStatement;
      int intf_offset;
      auto streq = sysmod.lookup("streq");
      assert(!!streq);
      void handleIntf(Intf intf) {
        // logln(name, ": offset for intf ", intf.name, ": ", intf_offset);
        as.stmts ~= iparse!(Statement, "cast_branch_intf", "tree.stmt")("if (streq(id, _test)) return void*:(void**:this + offs);",
          rf, "_test", mkString(intf.mangle_id), "offs", mkInt(intf_offset)
        );
        intf_offset ++;
      }
      void handleClass(Class cl) {
        as.stmts ~= fastcast!(Statement) (runTenthPure((void delegate(string,Object) dg) {
          dg("id", rf.lookup("id"));
          dg("this", rf.lookup("this"));
          dg("_test", fastcast!(Object) (mkString(cl.mangle_id)));
          dg("streq", sysmod.lookup("streq"));
        }, parseTenth(`
          (make-if
            (make-exprwrap (make-call streq (make-tuple-expr (list id _test))))
            '(make-return (reinterpret-cast (pointer-to (basic-type 'void)) this)))
        `)));
        if (cl.parent) handleClass(cl.parent);
        intf_offset = cl.classSize(false);
        doAlign(intf_offset, voidp);
        intf_offset /= 4;
        foreach (intf; cl.iparents)
          handleIntf(intf);
      }
      handleClass(this);
      as.stmts ~= iparse!(Statement, "cast_fallthrough", "tree.stmt")("return null; ", rf);
      rf.tree = sc;
      sc._body = as;
      current_module().entries ~= rf;
    }
  }
  // add interface refs
  void finalize() {
    genDefaultFuns;
    finalized = true;
    getClassinfo; // no-op to generate stuff
  }
  mixin TypeDefaults!();
  // this returns an Expr so that interface calls in a class method can resolve lazily, as they should.
  // interfaces come after the classinfo!
  Expr ownClassinfoLength() { // skipping interfaces
    return new CallbackExpr(Single!(SysInt), null, this /apply/ (Class self, Expr, AsmFile af) {
      self.parseMe;
      int res;
      if (self.parent) res += self.parent.getClassinfo().length;
      res += self.myfuns.funs.length;
      // logln("for ", self.name, ", res is ", res);
      mkInt(res).emitAsm(af);
    });
  }
  // array of .long-size literals; $ denotes a value, otherwise function - you know, gas syntax
  string[] getClassinfo(RelFunSet loverrides = Init!(RelFunSet)) { // local overrides
    parseMe;
    RelFunSet copy;
    copy.fillIn (loverrides);
    copy.fillIn (overrides);
    auto par = parent;
    while (par) {
      // use our parent's overriding functions to satisfy interfaces
      copy.fillIn (par.overrides);
      par = par.parent;
    }
    
    string[] res;
    // Liskov at work
    if (parent) res = parent.getClassinfo(copy);
    
    foreach (fun; myfuns.funs) {
      if (auto f2 = copy.hasLike(fun)) // if a child class overrode this, use its relfun
        res ~= f2.mangleSelf();
      else
        res ~= fun.mangleSelf();
    }
    
    // interfaces
    if (iparents.length) {
      int offset = classSize(false);
      doAlign(offset, voidp);
      offset /= 4; // steps of (void*).sizeof
      foreach (intf; iparents)
        res ~= intf.genClassinfo(offset, copy);
    }
    
    return res;
  }
  bool funAlreadyDefinedAbove(Function fun) {
    if (parent) parent.parseMe;
    if (parent && (
       parent.funAlreadyDefinedAbove(fun)
    || parent.myfuns.defines(fun))) return true;
    foreach (ipar; iparents) if (ipar.declares(fun.name)) return true;
    return false;
  }
  int classSize(bool withInterfaces) {
    parseMe;
    auto parentsize = parent?parent.classSize(true):0;
    auto res = max(voidp.size, parentsize, data.size());
    if (withInterfaces && iparents.length) {
      doAlign(res, voidp);
      getIntfLeaves((Intf) { res += voidp.size; });
    }
    return res;
  }
  // TODO
  mixin defaultIterate!();
  string ci_name() { return "classinfo_"~mangle(); }
  override {
    IType getRefType() {
      return new ClassRef(this);
    }
    void emitAsm(AsmFile af) {
      af.longstants[ci_name().dup] = getClassinfo().dup;
      if (weak) af.put(".weak ", ci_name());
    }
    int size() {
      // we return partial size so the struct thinks we contain our parent's struct
      // and thus puts its members at the right position
      if (!finalized) return classSize (false);
      return classSize (true);
    }
    void _add(string name, Object obj) {
      assert(!finalized, "Adding "~name~" to already-finalized class. ");
      if (auto fun = fastcast!(Function) (obj)) fun.sup = this;
      if (auto rf = fastcast!(RelFunction) (obj)) {
        if (funAlreadyDefinedAbove(rf))
          overrides.add(name, rf);
        else
          myfuns.funs ~= rf;
      } else {
        data._add(name, obj);
      }
    }
    string mangle(string name, IType type) {
      string typemangle;
      if (type) typemangle = "_of_"~type.mangle();
      return "class_"~this.name.cleanup()~"_"~name~typemangle;
    }
    Stuple!(IType, string, int)[] stackframe() {
      parseMe;
      Stuple!(IType, string, int)[] res;
      if (parent) res = parent.stackframe();
      res ~= selectMap!(RelMember, "stuple($.type, $.name, $.offset)");
      return res;
    }
    Object lookupRel(string str, Expr base) {
      if (!base && str == "__name") // T.name
        return fastcast!(Object) (mkString(name));
      auto crType = fastcast!(ClassRef) (resolveType(base.valueType()));
      if (!crType) {
        logln("Bad class ref: ", base, " of ", base.valueType());
        fail;
      }
      if (str == "this") return fastcast!(Object) (base);
      if (str == "super") return fastcast!(Object) (reinterpret_cast(new SuperType(crType), base));
      
      parseMe;
      
      if (auto res = data.lookup(str, true)) {
        if (auto rm = fastcast!(RelTransformable) (res)) {
          // logln("transform ", rm, " with ", base);
          return rm.transform(new DerefExpr(reinterpret_cast(new Pointer(data), base)));
        }
        return fastcast!(Object)~ res;
      }
      Extensible ext;
      if (auto res = myfuns.lookup(str, base)) {
        if (auto ext2 = fastcast!(Extensible) (res)) {
          if (ext) ext = ext.extend(res);
          else ext = ext2;
        } else return res;
      }
      Expr cl_offset = ownClassinfoLength;
      foreach (intf; iparents) {
        if (auto res = intf.lookupClass(str, cl_offset, base)) {
          auto obj = fastcast!(Object) (res);
          if (auto ext2 = fastcast!(Extensible) (res)) {
            if (ext) ext = ext.extend(obj);
            else ext = ext2;
          } else return obj;
        }
        cl_offset = foldex(lookupOp("+", cl_offset, mkInt(intf.clsize)));
      }
      if (parent) if (auto res = parent.lookupRel(str, base)) {
        if (auto ext2 = fastcast!(Extensible) (res)) {
          if (ext) ext = ext.extend(res);
          else ext = ext2;
        } else return res;
      }
      return fastcast!(Object) (ext);
    }
    Object lookup(string id, bool local = false) {
      parseMe;
      if (auto res = data.lookup(id, local)) return res;
      if (local) return null;
      if (auto rn = fastcast!(RelNamespace) (sup)) {
        if (ctx) {
          auto bp = fastcast!(Expr) (namespace().lookup("__base_ptr", true));
          if (bp) {
            bp = new DerefExpr(reinterpret_cast(new Pointer(data), bp));
            // logln(bp);
            // logln("for ", namespace());
            Object mew(Expr cref, RelNamespace rn) {
              cref = ctxFixup(cref);
              if (auto res = rn.lookupRel(id, cref))
                return res;
              return null;
            }
            Expr cref = fastcast!(Expr) (ctx.transform(bp));
            while (true) {
              if (auto res = mew(cref, rn)) return res;
              if (auto cl = fastcast!(Class) (rn)) {
                if (!cl.ctx) break;
                cref = fastcast!(Expr) (cl.ctx.transform(new DerefExpr(reinterpret_cast(new Pointer(cl.data), cref))));
                rn = fastcast!(RelNamespace) (cl.sup);
                if (!rn) break;
                continue;
              }
              break;
            }
          }
        }/* else {
          logln("use regular lookup (into rn) for ", id, " to ", sup);
          logln(" => ", sup.lookup(id, false));
        }*/
      }
      return sup.lookup(id, false);
    }
  }
}

// copypaste from ast/structure.d :(
Object gotClassDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  Class cl;
  if (!t2.gotIdentifier(name)) return null;
  auto t3 = t2;
  string sup;
  Class supclass;
  Intf[] supints;
  IType suptype;
  if (t3.accept(":"))
    if (!t3.bjoin(
      !!rest(t3, "type", &suptype),
      t3.accept(","),
      {
        t2 = t3;
        auto cr = fastcast!(ClassRef)  (suptype);
        auto ir = fastcast!(IntfRef) (suptype);
        if (!cr && !ir) throw new Exception("Cannot inherit from "~sup~": not a class or interface. ");
        if (ir) supints ~= ir.myIntf;
        else {
          if (ir) t3.failparse("Class must come first in inheritance spec");
          if (supclass) t3.failparse("Multiple inheritance is not supported");
          supclass = cr.myClass;
        }
      },
      false
  )) t3.failparse("Invalid inheritance spec");
  New(cl, name, supclass);
  cl.iparents = supints;
  
  auto classref = fastcast!(ClassRef) (cl.getRefType());
  namespace().add(classref);
  
  auto block = t2.coarseLexScope(true);
  
  cl.coarseSrc = block;
  cl.coarseCtx = namespace();
  addLate(&cl.parseMe);
  
  text = t2;
  return cast(Object) cl.getRefType();
}
mixin DefaultParser!(gotClassDef, "tree.typedef.class", null, "class");
mixin DefaultParser!(gotClassDef, "struct_member.nested_class", null, "class");

Object gotIntfDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!t2.gotIdentifier(name)) return null;
  auto t3 = t2;
  Intf[] supints;
  if (t3.accept(":")) {
    string sup;
    if (!t3.bjoin(
      t3.gotIdentifier(sup),
      t3.accept(","),
      {
        t2 = t3;
        auto supobj = namespace().lookup(sup);
        auto intf = fastcast!(IntfRef) (supobj);
        if (!intf) throw new Exception("Cannot inherit interface from "~sup~": not an interface. ");
        else supints ~= intf.myIntf;
      },
      false
    )) t3.failparse("Invalid interface inheritance spec");
  }
  bool predecl;
  if (!t2.accept("{") && !(t2.accept(";") && (predecl = true, true))) t2.failparse("Missing opening bracket for class def");
  auto intf = new Intf(name);
  intf.parents = supints;
  intf.initOffset;
  intf.predecl = predecl;
  bool reuse;
  if (!predecl) {
    auto pref = fastcast!(IntfRef) (namespace().lookup(name));
    if (pref && pref.myIntf.predecl) { intf = pref.myIntf; reuse = true; }
  }
  if (!reuse)
    namespace().add(intf.getRefType()); // support interface A { A foo(); }
  text = t2;
  if (predecl) return intf.getRefType();
  while (true) {
    auto fun = new Function;
    if (text.accept("}")) break;
    if (!gotGenericFunDecl(fun, cast(Namespace) null, false, text, cont, rest))
      text.failparse("Error parsing interface");
    intf.funs ~= fun;
  }
  return intf.getRefType();
}
mixin DefaultParser!(gotIntfDef, "tree.typedef.intf", null, "interface");

import ast.casting, ast.opers;

alias Single!(Pointer, Single!(Pointer, Single!(Void))) voidpp;

Expr intfToClass(Expr ex) {
  auto intpp = Single!(Pointer, Single!(Pointer, Single!(SysInt)));
  return reinterpret_cast(fastcast!(IType) (sysmod.lookup("Object")), lookupOp("+", reinterpret_cast(voidpp, ex), new DerefExpr(new DerefExpr(reinterpret_cast(intpp, ex)))));
}

void doImplicitClassCast(Expr ex, void delegate(Expr) dg) {
  void testIntf(Expr ex) {
    dg(ex);
    auto intf = (fastcast!(IntfRef)~ ex.valueType()).myIntf;
    int offs = 0;
    foreach (id, par; intf.parents) {
      auto nex = reinterpret_cast(new IntfRef(par), lookupOp("+", reinterpret_cast(voidpp, ex), mkInt(offs)));
      par.getLeaves((Intf) { offs++; });
      testIntf(nex);
    }
  }
  void testClass(Expr ex) {
    dg(ex);
    auto cl = (fastcast!(ClassRef) (ex.valueType())).myClass;
    if (!cl.parent && !cl.iparents) return; // just to clarify
    if (cl.parent) {
      testClass(reinterpret_cast(cl.parent.getRefType(), ex));
    }
    int offs = cl.classSize (false);
    doAlign(offs, voidp);
    offs /= 4;
    foreach (id, par; cl.iparents) {
      auto iex = reinterpret_cast(new IntfRef(par), lookupOp("+", reinterpret_cast(voidpp, ex), mkInt(offs)));
      par.getLeaves((Intf) { offs++; });
      testIntf(iex);
    }
  }
  auto cr = fastcast!(ClassRef)~ ex.valueType(), ir = fastcast!(IntfRef)~ ex.valueType();
  if (cr) testClass(ex);
  if (ir) testIntf(ex);
}

import ast.casting, ast.fold, tools.base: todg;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (fastcast!(IntfRef)~ ex.valueType())
      return intfToClass(ex);
    return null;
  };
  implicits ~= &doImplicitClassCast /todg;
  converts ~= delegate Expr(Expr ex, IType dest) {
    if (!fastcast!(ClassRef) (resolveType(dest)) && !fastcast!(IntfRef) (resolveType(dest)))
      return null;
    if (!gotImplicitCast(ex, delegate bool(IType it) {
      return fastcast!(ClassRef) (resolveType(it)) || fastcast!(IntfRef) (resolveType(it));
    }))
      return null;
    string dest_id;
    if (auto cr = fastcast!(ClassRef) (resolveType(dest))) dest_id = cr.myClass.mangle_id;
    else dest_id = (fastcast!(IntfRef) (resolveType(dest))).myIntf.mangle_id;
    
    bool isIntf;
    if (fastcast!(IntfRef) (resolveType(ex.valueType()))) isIntf = true;
    ex = reinterpret_cast(voidp, ex);
    return iparse!(Expr, "cast_call", "tree.expr")
      ("Dest:_fcc_dynamic_cast(ex, id, isIntf)",
        "ex", ex, "Dest", dest, "id", mkString(dest_id), "isIntf", mkInt(isIntf)
      );
  };
}