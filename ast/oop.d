module ast.oop;

import ast.parse, ast.base, ast.dg, ast.int_literal, ast.fun,
  ast.namespace, ast.structure, ast.structfuns, ast.pointer,
  ast.arrays, ast.aggregate, ast.literals, ast.slice, ast.nestfun;

import tools.log, tools.compat: max;
class VTable {
  RelFunction[] funs;
  Class parent;
  bool defines(string name) {
    foreach (fun; funs) if (fun.name == name) return true;
    return false;
  }
  Function lookup(string name, Expr classref) {
    int base = (parent.parent?parent.parent.getClassinfo().length:0);
    foreach (id, fun; funs)
      if (fun.name == name) {
        return new PointerFunction!(NestedFunction) (
          new DgConstructExpr(
            new DerefExpr(
              lookupOp("+",
                new DerefExpr(
                  reinterpret_cast(
                    new Pointer(new Pointer(fun.typeAsFp())),
                    classref)),
                new IntExpr(id+base))),
            reinterpret_cast(voidp, classref)));
      }
    return null;
  }
}

// lookupRel in interfaces/classes takes the class *reference*.
// This is IMPORTANT for compat with using.

class Intf : Named, IType, Tree, SelfAdding, RelNamespace {
  string name;
  override bool addsSelf() { return true; }
  override string getIdentifier() { return name; }
  mixin TypeDefaults!();
  override int size() { assert(false); }
  private this() { }
  mixin DefaultDup!();
  mixin defaultIterate!();
  override void emitAsm(AsmFile af) { }
  string toString() { return "interface "~name; }
  string mangle() { return "interface"; }
  Function[] funs;
  Intf[] parents;
  string mangle_id;
  this(string name) {
    this.name = name;
    mangle_id = namespace().mangle(name, this);
    logln(name, " => ", mangle_id);
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
  string[] genClassinfo(ref int offset, RelFunction[string] overrides) {
    string[] res;
    if (!parents.length)
      res ~= Format("-", offset++);
    else {
      res = parents[0].genClassinfo(offset, overrides);
      foreach (par; parents[1 .. $])
        res ~= par.genClassinfo(offset, overrides);
    }
    
    foreach (fun; funs)
      if (auto p = fun.name in overrides)
        res ~= p.mangleSelf();
      else
        throw new Exception(Format("Undefined2: ", name, " from ", this.name, "! "));
    
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
            new PA_Access(new DerefExpr(reinterpret_cast(pp_fntype, intp)), new IntExpr(id + own_offset)),
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
    if (!base) return lookupIntf(name, null);
    if (!cast(IntfRef) base.valueType()) {
      logln("Bad intf ref: ", base);
      asm { int 3; }
    }
    logln("intf lookup ", name, " in ", this.name);
    if (name == "this") return cast(Object) base;
    auto cv = cast(CValue) base;
    if (!cv) {
      logln("intf lookupRel fail ", base);
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
            new PA_Access(new DerefExpr(reinterpret_cast(pp_fntype, classref)), new IntExpr(id + own_offset + offs)),
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

class ClassRef : Type, SemiRelNamespace {
  Class myClass;
  this(Class cl) { myClass = cl; }
  override {
    RelNamespace resolve() { return myClass; }
    string toString() { return Format("ref ", myClass); }
    int size() { return nativePtrSize; }
    string mangle() { return "ref_"~myClass.mangle(); }
    int opEquals(IType type) {
      if (!super.opEquals(type)) return false;
      return myClass is (cast(ClassRef) type).myClass;
    }
  }
}

class IntfRef : Type, SemiRelNamespace {
  Intf myIntf;
  this(Intf i) { myIntf = i; }
  override {
    RelNamespace resolve() { return myIntf; }
    string toString() { return Format("ref ", myIntf); }
    int size() { return nativePtrSize; }
    string mangle() { return "intfref_"~myIntf.mangle(); }
    int opEquals(IType type) {
      if (!super.opEquals(type)) return false;
      return myIntf is (cast(IntfRef) type).myIntf;
    }
  }
}

import ast.modules;
class Class : Namespace, RelNamespace, Named, IType, Tree, SelfAdding, hasRefType {
  VTable myfuns;
  Structure data;
  string name;
  Class parent;
  Intf[] iparents;
  string toString() { return Format("class ", name); }
  void getIntfLeaves(void delegate(Intf) dg) {
    foreach (intf; iparents)
      intf.getLeaves(dg);
  }
  RelFunction[string] overrides;
  string mangle_id;
  override string mangle() { return mangle_id; }
  override bool addsSelf() { return true; }
  override Class dup() { assert(false, "wetfux! "); }
  this(string name, Class parent) {
    mangle_id = namespace().mangle(name, this);
    auto root = cast(Class) (sysmod?sysmod.lookup("Object"):null);
    if (root) {
      if (name == "Object")
        throw new Exception("Can't redefine Object! ");
    } else {
      if (name != "Object")
        throw new Exception("Object must be first class defined! ");
    }
    if (!parent) parent = root;
    this.name = name;
    New(data, cast(string) null);
    New(myfuns);
    myfuns.parent = this;
    this.parent = parent;
    if (!parent)
      new RelMember("classinfo", voidp, data);
  }
  bool finalized;
  void genDynCast() {
    auto rf = new RelFunction(this);
    New(rf.type);
    rf.name = "dynamicCastTo";
    rf.type.ret = voidp;
    rf.type.params ~= stuple(cast(IType) Single!(Array, Single!(Char)), "id");
    rf.sup = this;
    rf.fixup;
    add(rf);
    auto backup = namespace();
    namespace.set(rf);
    scope(exit) namespace.set(backup);
    // TODO: switch
    auto as = new AggrStatement;
    int intf_offset = mainSize();
    doAlign(intf_offset, voidp);
    intf_offset /= 4;
    auto strcmp = sysmod.lookup("strcmp");
    assert(!!strcmp);
    void handleIntf(Intf intf) {
      as.stmts ~= iparse!(Statement, "cast_intf_class", "tree.stmt")("if (strcmp(id, _test) != 0) return void*:(void**:this + offs); ",
        rf, "_test", mkString(intf.mangle_id), "offs", new IntExpr(intf_offset)
      );
      intf_offset ++;
    }
    void handleClass(Class cl) {
      as.stmts ~= iparse!(Statement, "cast_branch_class", "tree.stmt")("if (strcmp(id, _test) != 0) return void*:this; ",
        rf, "_test", mkString(cl.mangle_id)
      );
      if (cl.parent) handleClass(cl.parent);
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
    logln(name, ": ", data, " - ", size);
  }
  mixin TypeDefaults!();
  int ownClassinfoLength;
  // array of .long-size literals; $ denotes a value, otherwise function - you know, gas syntax
  string[] getClassinfo(RelFunction[string] loverrides = null) { // local overrides
    
    RelFunction[string] copy;
    foreach (key, value; loverrides)
      copy[key] = value;
    foreach (key, value; overrides)
      if (!(key in copy))
        copy[key] = value;
    
    string[] res;
    // Liskov at work
    if (parent) res = parent.getClassinfo(copy);
    
    foreach (fun; myfuns.funs) {
      if (auto p = fun.name in copy) // if a child class overrode this, use its relfun
        res ~= p.mangleSelf();
      else
        res ~= fun.mangleSelf();
    }
    
    ownClassinfoLength = res.length;
    
    // interfaces
    if (iparents.length) {
      int offset = mainSize();
      doAlign(offset, voidp);
      offset /= 4; // steps of (void*).sizeof
      foreach (intf; iparents)
        res ~= intf.genClassinfo(offset, copy);
    }
    
    return res;
  }
  bool funAlreadyDefined(string name) {
    if (parent && parent.funAlreadyDefined(name)) return true;
    if (myfuns.defines(name)) return true;
    foreach (ipar; iparents) if (ipar.declares(name)) return true;
    return false;
  }
  // everything after this is interface handles - I think
  int mainSize() { return max(voidp.size, parent?parent.mainSize():0, data.size()); }
  // TODO
  mixin defaultIterate!();
  string ci_name() { return "classinfo_"~mangle(); }
  override {
    IType getRefType() {
      return new ClassRef(this);
    }
    string getIdentifier() {
      return name;
    }
    void emitAsm(AsmFile af) {
      af.longstants[ci_name()] = getClassinfo();
    }
    int size() {
      // HAAAAAAAAAAAAAAAAAAX
      // we return mainsize so the struct thinks we contain our parent's struct
      // and thus puts its members after the parent's
      if (!finalized) return mainSize;
      auto res = data.size; // already includes parent's size
      if (iparents.length) {
        doAlign(res, voidp);
        getIntfLeaves((Intf) { res += voidp.size; });
      }
      return res;
    }
    void _add(string name, Object obj) {
      assert(!finalized, "Adding "~name~" to already-finalized class. ");
      if (auto rf = cast(RelFunction) obj) {
        if (funAlreadyDefined(name))
          overrides[name] = rf;
        else
          myfuns.funs ~= rf;
      } else {
        data._add(name, obj);
      }
    }
    string mangle(string name, IType type) {
      return "class_"~this.name~"_"~name~"_of_"~type.mangle();
    }
    Stuple!(IType, string, int)[] stackframe() {
      Stuple!(IType, string, int)[] res;
      if (parent) res = parent.stackframe();
      res ~= selectMap!(RelMember, "stuple($.type, $.name, $.offset)");
      return res;
    }
    Object lookupRel(string str, Expr base) {
      if (!cast(ClassRef) base.valueType()) {
        logln("Bad class ref: ", base, " of ", base.valueType());
        asm { int 3; }
      }
      if (str == "this") return cast(Object) base;
      if (auto res = data.lookup(str, true)) {
        if (auto rm = cast(RelMember) res) {
          // logln("transform ", rm, " with ", base);
          return rm.transform(new DerefExpr(reinterpret_cast(new Pointer(data), base)));
        }
        return cast(Object) res;
      }
      if (auto res = myfuns.lookup(str, base)) {
        return cast(Object) res;
      }
      int cl_offset = ownClassinfoLength;
      foreach (intf; iparents) {
        if (auto res = intf.lookupClass(str, cl_offset, base))
          return cast(Object) res;
        cl_offset += intf.clsize;
      }
      if (parent) if (auto res = parent.lookupRel(str, base)) {
        return res;
      }
      return sup.lookup(str, false); // defer
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
  if (t3.accept(":"))
    if (!t3.bjoin(
      t3.gotIdentifier(sup),
      t3.accept(","),
      {
        t2 = t3;
        auto supobj = namespace().lookup(sup);
        auto cl = cast(Class) supobj;
        auto intf = cast(Intf) supobj;
        if (!cl && !intf) throw new Exception("Cannot inherit from "~sup~": not a class or interface. ");
        if (intf) supints ~= intf;
        else {
          if (intf) t3.failparse("Class must come first in inheritance spec");
          if (supclass) t3.failparse("Multiple inheritance is not supported");
          supclass = cl;
        }
      },
      false
  )) t3.failparse("Invalid inheritance spec");
  if (!t2.accept("{")) t2.failparse("Missing opening bracket for class def");
  New(cl, name, supclass);
  cl.iparents = supints;
  namespace().add(cl); // add here so as to allow self-refs in body
  if (matchStructBody(t2, cl, cont, rest)) {
    if (!t2.accept("}"))
      t2.failparse("Failed to parse struct body");
    // logln("register class ", cl.name);
    text = t2;
    cl.finalize;
    return cl;
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
        auto intf = cast(Intf) supobj;
        if (!intf) throw new Exception("Cannot inherit interface from "~sup~": not an interface. ");
        else supints ~= intf;
      },
      false
    )) t3.failparse("Invalid interface inheritance spec");
  }
  if (!t2.accept("{")) t2.failparse("Missing opening bracket for class def");
  auto intf = new Intf(name);
  intf.parents = supints;
  intf.initOffset;
  namespace().add(intf); // support interface A { A foo(); }
  text = t2;
  while (true) {
    auto fun = new Function;
    if (text.accept("}")) break;
    if (!gotGenericFunDecl(fun, cast(Namespace) null, false, text, cont, rest))
      text.failparse("Error parsing interface");
    intf.funs ~= fun;
  }
  return intf;
}
mixin DefaultParser!(gotIntfDef, "tree.typedef.intf", null, "interface");

Object gotClassRef(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    retry:
    if (auto cl = cast(Class) namespace().lookup(id)) {
      text = t2;
      return new ClassRef(cl);
    } else if (t2.eatDash(id)) goto retry;
  }
  return null;
}
mixin DefaultParser!(gotClassRef, "type.class", "35"); // before type.named

Object gotIntfRef(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    retry:
    if (auto i = cast(Intf) namespace().lookup(id)) {
      text = t2;
      return new IntfRef(i);
    } else if (t2.eatDash(id)) goto retry;
  }
  return null;
}
mixin DefaultParser!(gotIntfRef, "type.intf", "36"); // before type.named

// ruefully copypasted from ast.structure
Object gotClassMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  t2.passert(!!lhs_partial(),
    "got class member expr? weird");
  auto ex = cast(Expr) lhs_partial();
  if (!ex) return null;
  auto cr = cast(ClassRef) ex.valueType(), ir = cast(IntfRef) ex.valueType();
  if (!cr && !ir) return null;
  Class cl; Intf intf;
  if (cr) cl = cr.myClass;
  else intf = ir.myIntf;
  
  string member;
  
  if (t2.accept(".") && t2.gotIdentifier(member)) {
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
mixin DefaultParser!(gotClassMemberExpr, "tree.rhs_partial.access_class_member");

import ast.casting, ast.opers;

alias Single!(Pointer, Single!(Pointer, Single!(Void))) voidpp;

Expr intfToClass(Expr ex) {
  auto intpp = Single!(Pointer, Single!(Pointer, Single!(SysInt)));
  return new RCE(new ClassRef(cast(Class) sysmod.lookup("Object")), lookupOp("+", new RCE(voidpp, ex), new DerefExpr(new DerefExpr(new RCE(intpp, ex)))));
}

void doImplicitClassCast(Expr ex, void delegate(Expr) dg) {
  void testIntf(Expr ex) {
    dg(ex);
    auto intf = (cast(IntfRef) ex.valueType()).myIntf;
    int offs = 0;
    foreach (id, par; intf.parents) {
      auto nex = new RCE(new IntfRef(par), lookupOp("+", new RCE(voidpp, ex), new IntExpr(offs)));
      par.getLeaves((Intf) { offs++; });
      testIntf(nex);
    }
  }
  void testClass(Expr ex) {
    dg(ex);
    auto cl = (cast(ClassRef) ex.valueType()).myClass;
    if (!cl.parent && !cl.iparents) return; // just to clarify
    if (cl.parent) {
      testClass(new RCE(new ClassRef(cl.parent), ex));
    }
    int offs = cl.mainSize();
    doAlign(offs, voidp);
    offs /= 4;
    foreach (id, par; cl.iparents) {
      auto iex = new RCE(new IntfRef(par), lookupOp("+", new RCE(voidpp, ex), new IntExpr(offs)));
      par.getLeaves((Intf) { offs++; });
      testIntf(iex);
    }
  }
  auto cr = cast(ClassRef) ex.valueType(), ir = cast(IntfRef) ex.valueType();
  if (cr) testClass(ex);
  if (ir) testIntf(ex);
}

import ast.casting, tools.base: todg;
static this() {
  implicits ~= delegate Expr(Expr ex) {
    if (cast(IntfRef) ex.valueType())
      return intfToClass(ex);
    return null;
  };
  implicits ~= &doImplicitClassCast /todg;
}

Object gotDynCast(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  IType dest;
  if (!rest(t2, "type", &dest) || !t2.accept(":"))
    return null;
  if (!cast(ClassRef) dest && !cast(IntfRef) dest)
    return null;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex)) {
    return null;
  }
  if (!cast(ClassRef) ex.valueType() && !cast(IntfRef) ex.valueType())
    return null;
  text = t2;
  
  {
    Expr res;
    doImplicitClassCast(ex, (Expr ex) {
      if (res) return;
      if (ex.valueType() == dest) res = ex;
    });
    if (res) return cast(Object) res;
  }
  
  string dest_id;
  if (auto cr = cast(ClassRef) dest) dest_id = cr.myClass.mangle_id;
  else dest_id = (cast(IntfRef) dest).myIntf.mangle_id;
  
  if (cast(IntfRef) ex.valueType()) ex = intfToClass(ex);
  return cast(Object) iparse!(Expr, "cast_call", "tree.expr")
    ("Dest:ex.dynamicCastTo(id)", "ex",
      ex, "Dest", dest, "id", mkString(dest_id)
    );
}
mixin DefaultParser!(gotDynCast, "tree.expr.dynamic_class_cast", "70");
