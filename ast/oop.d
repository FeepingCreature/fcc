module ast.oop;

import ast.parse, ast.base, ast.dg, ast.int_literal, ast.fun,
  ast.namespace, ast.structure, ast.structfuns, ast.pointer,
  ast.arrays, ast.aggregate, ast.literals, ast.slice;

import tools.log;
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
        return iparse!(Function, "vtable_lookup", "tree.expr")(
          "*(*cast(fntype**) &classref)[id + base].toDg(cast(void*) &classref)",
          "classref", classref,
          "id", new IntExpr(id), "base", new IntExpr(base),
          "fntype", fun.typeAsFp()
        );
      }
    return null;
  }
}

class Intf : Named, IType, Tree {
  string name;
  override string getIdentifier() { return name; }
  mixin TypeDefaults!();
  override int size() { assert(false); }
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
  Function lookupIntf(string name, Expr intp) {
    assert(own_offset);
    foreach (id, fun; funs) {
      if (fun.name == name) {
        return iparse!(Function, "intf_vtable_lookup", "tree.expr")
        ( "
            *(*cast(fntype**) intp)[id].toDg(cast(void**) intp + **cast(int**) intp)
          ",
          "fntype", fun.getPointer().valueType(), "intp", intp,
          "id", new IntExpr(id + own_offset)
        );
      }
    }
    return null;
  }
  Function lookupClass(string name, int offs, Expr classref) {
    assert(own_offset, this.name~": interface lookup for "~name~" but classinfo uninitialized. ");
    foreach (id, fun; funs) {
      if (fun.name == name) {
        return iparse!(Function, "intf_vtable_lookup2", "tree.expr")
        ( "
            *(*cast(fntype**) &classref)[id + offs].toDg(cast(void*) &classref)
          ",
          "fntype", fun.getPointer().valueType(), "classref", classref,
          "id", new IntExpr(id + own_offset), "offs", new IntExpr(offs)
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

class ClassRef : Type {
  Class myClass;
  this(Class cl) { myClass = cl; }
  override {
    string toString() { return Format("ref ", myClass); }
    int size() { return nativePtrSize; }
    string mangle() { return "class_"~myClass.name; }
    int opEquals(IType type) {
      if (!super.opEquals(type)) return false;
      return myClass is (cast(ClassRef) type).myClass;
    }
  }
}

class IntfRef : Type {
  Intf myIntf;
  this(Intf i) { myIntf = i; }
  override {
    string toString() { return Format("ref ", myIntf); }
    int size() { return nativePtrSize; }
    string mangle() { return "intf_"~myIntf.name; }
    int opEquals(IType type) {
      if (!super.opEquals(type)) return false;
      return myIntf is (cast(IntfRef) type).myIntf;
    }
  }
}

import ast.modules;
class Class : Namespace, RelNamespace, Named, IType, Tree {
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
  override string mangle() { return "class"; }
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
    as.stmts ~= iparse!(Statement, "cast_log", "tree.stmt")(`writeln("cast $$typeof(this).stringof to id. "); `, rf);
    int intf_offset = mainSize();
    doAlign(intf_offset, voidp);
    intf_offset /= 4;
    auto strcmp = sysmod.lookup("strcmp");
    assert(!!strcmp);
    void handleIntf(Intf intf) {
      as.stmts ~= iparse!(Statement, "cast_intf_class", "tree.stmt")("if (strcmp(id, _test) != 0) return cast(void*) (cast(void**) this + offs); ",
        rf, "_test", new StringExpr(intf.mangle_id), "offs", new IntExpr(intf_offset)
      );
      intf_offset ++;
    }
    void handleClass(Class cl) {
      as.stmts ~= iparse!(Statement, "cast_branch_class", "tree.stmt")("if (strcmp(id, _test) != 0) return cast(void*) this; ",
        rf, "_test", new StringExpr(cl.mangle_id)
      );
      if (cl.parent) handleClass(cl.parent);
      foreach (intf; cl.iparents)
        handleIntf(intf);
    }
    handleClass(this);
    as.stmts ~= iparse!(Statement, "cast_fallthrough", "tree.stmt")("return cast(void*) 0; ", rf);
    rf.tree = as;
    get!(Module).entries ~= rf;
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
  int mainSize() { return (parent?parent.size():0) + data.size(); }
  // TODO
  mixin defaultIterate!();
  string ci_name() { return "classinfo_"~name; }
  override {
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
      select((string, RelMember rm) {
        res ~= stuple(rm.type, rm.name, rm.offset);
      });
      return res;
    }
    Object lookupRel(string str, Expr base) {
      // logln("rel lookup for ", str, " in ", base);
      if (str == "this") return new RefExpr(cast(CValue) base);
      if (auto res = data.lookup(str, true)) {
        if (auto rm = cast(RelMember) res) {
          // logln("transform ", rm, " with ", base);
          return rm.transform(
            iparse!(Expr, "rel_struct_cast", "tree.expr")
            ("*cast(data*) &base", "data", data, "base", base)
          );
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
  if (!t2.accept("class ")) return null;
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
          if (intf) throw new Exception("Class must come first in inheritance spec: '"~t3.next_text()~"'");
          if (supclass) throw new Exception("Multiple inheritance is not supported: '"~t3.next_text()~"'");
          supclass = cl;
        }
      },
      false
  )) throw new Exception("Invalid inheritance spec at '"~t3.next_text()~"'");
  if (!t2.accept("{")) throw new Exception("Missing opening bracket for class def! ");
  New(cl, name, supclass);
  cl.iparents = supints;
  cl.sup = namespace();
  namespace().add(cl); // add here so as to allow self-refs in body
  if (matchStructBody(t2, cl, cont, rest)) {
    if (!t2.accept("}"))
      throw new Exception("Missing closing bracket at "~t2.next_text());
    // logln("register class ", cl.name);
    text = t2;
    cl.finalize;
    return cl;
  } else {
    throw new Exception("Couldn't match structure body at "~t2.next_text());
  }
}
mixin DefaultParser!(gotClassDef, "tree.typedef.class");

Object gotIntfDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("interface ")) return null;
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
    )) throw new Exception("Invalid interface inheritance spec at '"~t3.next_text()~"'");
  }
  if (!t2.accept("{")) throw new Exception("Missing opening bracket for class def! ");
  auto intf = new Intf(name);
  intf.parents = supints;
  intf.initOffset;
  while (true) {
    auto fun = new Function;
    if (t2.accept("}")) break;
    if (!gotGenericFunDecl(fun, cast(Namespace) null, false, t2, cont, rest))
      throw new Exception("Error parsing interface at '"~t2.next_text()~"'");
    intf.funs ~= fun;
  }
  namespace().add(intf);
  text = t2;
  return intf;
}
mixin DefaultParser!(gotIntfDef, "tree.typedef.intf");

Object gotClassRef(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    if (auto cl = cast(Class) namespace().lookup(id)) {
      text = t2;
      return new ClassRef(cl);
    }
  }
  return null;
}
mixin DefaultParser!(gotClassRef, "type.class", "35"); // before type.named

Object gotIntfRef(ref string text, ParseCb cont, ParseCb rest) {
  string id, t2 = text;
  if (t2.gotIdentifier(id)) {
    if (auto i = cast(Intf) namespace().lookup(id)) {
      text = t2;
      return new IntfRef(i);
    }
  }
  return null;
}
mixin DefaultParser!(gotIntfRef, "type.intf", "36"); // before type.named

// ruefully copypasted from ast.structure
Object gotClassMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  assert(lhs_partial());
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
    if (cl) m = cl.lookupRel(member, iparse!(Expr, "class_ptr_access", "tree.expr")("*cast(Cl*) hdl", "Cl", cl, "hdl", ex));
    else m = intf.lookupIntf(member, ex);
    text = t2;
    return m;
  } else return null;
}
mixin DefaultParser!(gotClassMemberExpr, "tree.rhs_partial.access_class_member");

import ast.casting, ast.math;

alias ReinterpretCast!(Expr) RCE;
alias Single!(Pointer, Single!(Pointer, Single!(Void))) voidpp;

Expr intfToClass(Expr ex) {
  auto intpp = Single!(Pointer, Single!(Pointer, Single!(SysInt)));
  return new RCE(new ClassRef(cast(Class) sysmod.lookup("Object")), new AddExpr(new RCE(voidpp, ex), new DerefExpr(new DerefExpr(new RCE(intpp, ex)))));
}

Object gotImplicitCastToObject(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr ^selfrule", &ex, (Expr ex) { return !!cast(IntfRef) ex.valueType(); }))
    return null;
  text = t2;
  // any object is an Object.
  return cast(Object) intfToClass(ex);
}
mixin DefaultParser!(gotImplicitCastToObject, "tree.expr.implicit_intf_cast_to_obj", "9020");

Object doImplicitClassCast(Expr ex, ParseCtl delegate(Object) accept) {
  bool abort;
  Expr testIntf(Expr ex) {
    auto ac = accept(cast(Object) ex);
    if (ac == ParseCtl.AcceptCont || ac == ParseCtl.AcceptAbort) return ex;
    if (ac == ParseCtl.RejectAbort) { abort = true; return null; }
    auto intf = (cast(IntfRef) ex.valueType()).myIntf;
    int offs = 0;
    foreach (id, par; intf.parents) {
      auto nex = new RCE(new IntfRef(par), new AddExpr(new RCE(voidpp, ex), new IntExpr(offs)));
      par.getLeaves((Intf) { offs++; });
      if (auto res = testIntf(nex)) return res;
      if (abort) break;
    }
    return null;
  }
  Expr testClass(Expr ex) {
    auto ac = accept(cast(Object) ex);
    if (ac == ParseCtl.AcceptCont || ac == ParseCtl.AcceptAbort) return ex;
    if (ac == ParseCtl.RejectAbort) { abort = true; return null; }
    auto cl = (cast(ClassRef) ex.valueType()).myClass;
    if (!cl.parent && !cl.iparents) return null; // just to clarify
    if (cl.parent) {
      auto pex = new RCE(new ClassRef(cl.parent), ex);
      if (auto res = testClass(pex))
        return res;
      if (abort) return null;
    }
    int offs = cl.mainSize();
    doAlign(offs, voidp);
    offs /= 4;
    foreach (id, par; cl.iparents) {
      auto iex = new RCE(new IntfRef(par), new AddExpr(new RCE(voidpp, ex), new IntExpr(offs)));
      par.getLeaves((Intf) { offs++; });
      if (auto res = testIntf(iex)) return res;
      if (abort) break;
    }
    return null;
  }
  auto cr = cast(ClassRef) ex.valueType(), ir = cast(IntfRef) ex.valueType();
  if (cr) {
    if (auto res = testClass(ex)) return cast(Object) res;
  }
  if (ir) {
    if (auto res = testIntf(ex)) return cast(Object) res;
  }
  return null;
}

Object gotImplicitClassCast(ref string text, ParseCtl delegate(Object) accept, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr ^selfrule", &ex)) return null;
  if (auto res = doImplicitClassCast(ex, accept)) { text = t2; return res; }
  return null;
}
mixin DefaultParser!(gotImplicitClassCast, "tree.expr.implicit_class_cast", "902");

Object gotDynCast(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto t2 = text;
  if (!t2.accept("cast(")) return null;
  IType dest;
  if (!rest(t2, "type", &dest))
    return null;
  if (!t2.accept(")"))
    throw new Exception("Missed closing bracket in class cast at '"~t2.next_text()~"'");
  if (!cast(ClassRef) dest && !cast(IntfRef) dest)
    return null;
  if (!rest(t2, "tree.expr >tree.expr.arith", &ex))
    return null;
  if (!cast(ClassRef) ex.valueType() && !cast(IntfRef) ex.valueType())
    return null;
  text = t2;
  
  if (auto res = doImplicitClassCast(ex, (Object obj) {
    auto ex = cast(Expr) obj;
    if (ex.valueType() == dest)
      return ParseCtl.AcceptAbort;
    else
      return ParseCtl.RejectCont;
  })) return res;
  
  string dest_id;
  if (auto cr = cast(ClassRef) dest) dest_id = cr.myClass.mangle_id;
  else dest_id = (cast(IntfRef) dest).myIntf.mangle_id;
  
  if (cast(IntfRef) ex.valueType()) ex = intfToClass(ex);
  return cast(Object) iparse!(Expr, "cast_call", "tree.expr")
    ("cast(Dest) ex.dynamicCastTo(id)", "ex",
      ex, "Dest", dest, "id", new StringExpr(dest_id)
    );
}
mixin DefaultParser!(gotDynCast, "tree.expr.dynamic_class_cast", "70");
