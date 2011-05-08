module ast.oop;

import ast.parse, ast.base, ast.dg, ast.int_literal, ast.fun,
  ast.namespace, ast.structure, ast.structfuns, ast.pointer,
  ast.arrays, ast.aggregate, ast.literals, ast.slice, ast.nestfun;

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
  bool defines(Function fun) {
    foreach (f2; funs)
      if (f2.name == fun.name &&
          f2.getParams() == fun.getParams()) return true;
    return false;
  }
  Object lookup(string name, Expr classref) {
    int base = (parent.parent?parent.parent.getClassinfo().length:0);
    Function[] res;
    foreach (id, fun; funs)
      if (fun.name == name) {
        classref = lvize(classref);
        // logln("in ", parent.name, ", ", fun.name, " is @", id, " (base ", base, ")");
        res ~= new PointerFunction!(NestedFunction) (
          new DgConstructExpr(
            new DerefExpr(
              lookupOp("+",
                new DerefExpr(
                  reinterpret_cast(
                    new Pointer(new Pointer(fun.typeAsFp())),
                    classref)),
                mkInt(id+base))),
            reinterpret_cast(voidp, classref)));
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
  mixin TypeDefaults!();
  override int size() { assert(false); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override void emitAsm(AsmFile af) { }
  override bool isTempNamespace() { return false; }
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
  Function lookupIntf(string name, Expr intp) {
    assert(own_offset);
    foreach (id, fun; funs) {
      if (fun.name == name) {
        if (!intp) return fun;
        auto fntype = fun.getPointer().valueType();
        auto pp_fntype = new Pointer(new Pointer(fntype));
        auto pp_int = Single!(Pointer, Single!(Pointer, Single!(SysInt)));
        // *(*fntype**:intp)[id].toDg(void**:intp + **int**:intp)
        return new PointerFunction!(NestedFunction)(
          new DgConstructExpr(
            new PA_Access(new DerefExpr(reinterpret_cast(pp_fntype, intp)), mkInt(id + own_offset)),
            lookupOp("+",
              reinterpret_cast(new Pointer(voidp), intp),
              new DerefExpr(new DerefExpr(reinterpret_cast(pp_int, intp)))
            )
          )
        );
      }
    }
    return null;
  }
  override Object lookupRel(string name, Expr base) {
    if (!base) {
      if (name == "name") // T.name
        return fastcast!(Object) (mkString(this.name));
      return lookupIntf(name, null);
    }
    if (!fastcast!(IntfRef) (base.valueType())) {
      logln("Bad intf ref: ", base);
      asm { int 3; }
    }
    if (name == "this") return fastcast!(Object)~ base;
    auto cv = fastcast!(CValue)~ base;
    if (!cv) {
      // logln("intf lookupRel fail ", base);
      return null;
    }
    auto self = new RefExpr(cv);
    return lookupIntf(name, self);
  }
  Function lookupClass(string name, int offs, Expr classref) {
    assert(own_offset, this.name~": interface lookup for "~name~" but classinfo uninitialized. ");
    foreach (id, fun; funs) {
      if (fun.name == name) {
        // *(*fntype**:classref)[id + offs].toDg(void*:classref)
        auto fntype = fun.getPointer().valueType();
        auto pp_fntype = new Pointer(new Pointer(fntype));
        return new PointerFunction!(NestedFunction)(
          new DgConstructExpr(
            new PA_Access(new DerefExpr(reinterpret_cast(pp_fntype, classref)), mkInt(id + own_offset + offs)),
            reinterpret_cast(voidp, classref)
          )
        );
      }
    }
    foreach (par; parents) {
      if (auto res = par.lookupClass(name, offs, classref)) return res;
      offs += par.clsize;
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
  this(Class cl) { myClass = cl; if (!cl) asm { int 3; } }
  override {
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
      return myClass is (fastcast!(ClassRef) (resolveType(type))).myClass;
    }
    Expr format(Expr ex) {
      return mkString("ref to "~myClass.name);
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
    Object lookupRel(string name, Expr base) {
      auto sup2 = fastcast!(SuperType) (base.valueType());
      if (sup2 !is this) asm { int 3; }
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
  }
}

import ast.modules;
class Class : Namespace, RelNamespace, IType, Tree, hasRefType {
  VTable myfuns;
  Structure data;
  string name;
  Class parent;
  Intf[] iparents;
  string toString() { return Format("class ", name, " <- ", sup); }
  void getIntfLeaves(void delegate(Intf) dg) {
    foreach (intf; iparents)
      intf.getLeaves(dg);
  }
  RelFunSet overrides;
  string mangle_id;
  bool weak;
  void markWeak() { weak = true; foreach (fun; myfuns.funs) (fastcast!(IsMangled) (fun)).markWeak(); }
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
      data = parent.data.dup();
    }
    sup = namespace();
  }
  bool finalized;
  void genDynCast() {
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
      as.stmts ~= iparse!(Statement, "cast_branch_class", "tree.stmt")("if (streq(id, _test)) return void*:this;",
        rf, "_test", mkString(cl.mangle_id)
      );
      if (cl.parent) handleClass(cl.parent);
      intf_offset = cl.classSize(false);
      doAlign(intf_offset, voidp);
      intf_offset /= 4;
      foreach (intf; cl.iparents)
        handleIntf(intf);
    }
    handleClass(this);
    as.stmts ~= iparse!(Statement, "cast_fallthrough", "tree.stmt")("return null; ", rf);
    rf.tree = as;
    current_module().entries ~= rf;
  }
  // add interface refs
  void finalize() {
    genDynCast;
    finalized = true;
    getClassinfo; // no-op to generate stuff
  }
  mixin TypeDefaults!();
  int ownClassinfoLength() { // skipping interfaces
    int res;
    if (parent) res += parent.getClassinfo().length;
    res += myfuns.funs.length;
    return res;
  }
  // array of .long-size literals; $ denotes a value, otherwise function - you know, gas syntax
  string[] getClassinfo(RelFunSet loverrides = Init!(RelFunSet)) { // local overrides
    
    RelFunSet copy;
    copy.fillIn (loverrides);
    copy.fillIn (overrides);
    
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
    if (parent && (
       parent.funAlreadyDefinedAbove(fun)
    || parent.myfuns.defines(fun))) return true;
    foreach (ipar; iparents) if (ipar.declares(fun.name)) return true;
    return false;
  }
  int classSize(bool withInterfaces) {
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
      af.longstants[ci_name()] = getClassinfo();
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
      return "class_"~this.name.cleanup()~"_"~name~"_of_"~type.mangle();
    }
    Stuple!(IType, string, int)[] stackframe() {
      Stuple!(IType, string, int)[] res;
      if (parent) res = parent.stackframe();
      res ~= selectMap!(RelMember, "stuple($.type, $.name, $.offset)");
      return res;
    }
    Object lookupRel(string str, Expr base) {
      if (!base && str == "name") // T.name
        return fastcast!(Object) (mkString(name));
      auto crType = fastcast!(ClassRef) (resolveType(base.valueType()));
      if (!crType) {
        logln("Bad class ref: ", base, " of ", base.valueType());
        asm { int 3; }
      }
      if (str == "this") return fastcast!(Object) (base);
      if (str == "super") return fastcast!(Object) (reinterpret_cast(new SuperType(crType), base));
      if (auto res = data.lookup(str, true)) {
        if (auto rm = fastcast!(RelTransformable) (res)) {
          // logln("transform ", rm, " with ", base);
          return rm.transform(new DerefExpr(reinterpret_cast(new Pointer(data), base)));
        }
        return fastcast!(Object)~ res;
      }
      if (auto res = myfuns.lookup(str, base)) {
        return res;
      }
      int cl_offset = ownClassinfoLength;
      foreach (intf; iparents) {
        if (auto res = intf.lookupClass(str, cl_offset, base))
          return fastcast!(Object)~ res;
        cl_offset += intf.clsize;
      }
      if (parent) if (auto res = parent.lookupRel(str, base)) {
        return res;
      }
      // NUH!! 
      // return sup.lookup(str, false); // defer
      return null;
    }
    Object lookup(string id, bool local = false) {
      if (auto res = data.lookup(id, local)) return res;
      if (local) return null;
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
  if (!t2.accept("{")) t2.failparse("Missing opening bracket for class def");
  New(cl, name, supclass);
  cl.iparents = supints;
  namespace().add(fastcast!(ClassRef) (cl.getRefType())); // add here so as to allow self-refs in body
  if (matchStructBody(t2, cl, cont, rest)) {
    if (!t2.accept("}"))
      t2.failparse("Failed to parse struct body");
    // logln("register class ", cl.name);
    try cl.finalize;
    catch (Exception ex) text.failparse(ex);
    text = t2;
    return cast(Object) cl.getRefType();
  } else {
    t2.failparse("Couldn't match structure body");
  }
}
mixin DefaultParser!(gotClassDef, "tree.typedef.class", null, "class");

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
  if (!t2.accept("{")) t2.failparse("Missing opening bracket for class def");
  auto intf = new Intf(name);
  intf.parents = supints;
  intf.initOffset;
  namespace().add(intf.getRefType()); // support interface A { A foo(); }
  text = t2;
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

// ruefully copypasted from ast.structure
Object gotClassMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  t2.passert(!!lhs_partial(),
    "got class member expr? weird");
  auto ex = fastcast!(Expr) (lhs_partial());
  if (!ex) return null;
  if (!gotImplicitCast(ex, (IType it) {
    it = resolveType(it);
    return fastcast!(ClassRef) (it) || fastcast!(IntfRef) (it);
  })) return null;
  auto it = ex.valueType();
  it = resolveType(it);
  
  auto cr = fastcast!(ClassRef) (it), ir = fastcast!(IntfRef) (it);
  if (!cr && !ir) return null;
  
  Class cl; Intf intf;
  if (cr) cl = cr.myClass;
  else intf = ir.myIntf;
  
  string member;
  
  if (t2.gotIdentifier(member)) {
    Object m;
    retry:
    if (cl) m = cl.lookupRel(member, ex);
    else m = intf.lookupIntf(member, ex);
    if (!m) {
      if (t2.eatDash(member)) goto retry;
      text.setError("No '", member, "' in ", cl?cl:intf, "!");
      return null;
    }
    text = t2;
    return m;
  } else return null;
}
mixin DefaultParser!(gotClassMemberExpr, "tree.rhs_partial.access_class_member", null, ".");

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