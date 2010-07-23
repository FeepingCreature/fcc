module ast.oop;

import ast.parse, ast.base, ast.dg, ast.int_literal, ast.fun,
  ast.namespace, ast.structure, ast.structfuns, ast.pointer;

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

class ClassRef : Type {
  Class myClass;
  this(Class cl) { myClass = cl; }
  override {
    int size() { return nativePtrSize; }
    string mangle() { return "class_"~myClass.name; }
  }
}

class Class : Namespace, RelNamespace, Named, IType, Tree {
  VTable myfuns;
  Structure data;
  string name;
  Class parent;
  RelFunction[string] overrides;
  this(string name) {
    this.name = name;
    New(data, cast(string) null);
    New(myfuns);
    myfuns.parent = this;
    new RelMember("classinfo", Single!(Pointer, Single!(Void)), data);
  }
  mixin TypeDefaults!();
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
      if (auto p = fun.name in copy) // if a superclass overrode this, use its relfun
        res ~= p.mangleSelf();
      else
        res ~= fun.mangleSelf();
    }
    
    return res;
  }
  bool funAlreadyDefined(string name) {
    if (parent && parent.funAlreadyDefined(name)) return true;
    if (myfuns.defines(name)) return true;
    return false;
  }
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
    int size() { return (parent?parent.size():0) + data.size(); }
    string mangle() { return "classdata_of_"~name; }
    void _add(string name, Object obj) {
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
  string sup; Class supclass;
  if (t3.accept(":") && t3.gotIdentifier(sup)) {
    t2 = t3;
    supclass = cast(Class) namespace().lookup(sup);
    if (!supclass) throw new Exception("Cannot inherit from "~sup~": not a class. ");
  }
  if (!t2.accept("{")) throw new Exception("Missing opening bracket for class def! ");
  New(cl, name);
  cl.parent = supclass;
  cl.sup = namespace();
  if (matchStructBody(t2, cl, cont, rest)) {
    if (!t2.accept("}"))
      throw new Exception("Missing closing bracket at "~t2.next_text());
    // logln("register class ", cl.name);
    namespace().add(cl);
    text = t2;
    return cl;
  } else {
    throw new Exception("Couldn't match structure body at "~t2.next_text());
  }
}
mixin DefaultParser!(gotClassDef, "tree.typedef.class");

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

// ruefully copypasted from ast.structure
Object gotClassMemberExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  assert(lhs_partial());
  auto ex = cast(Expr) lhs_partial();
  if (!ex) return null;
  auto cr = cast(ClassRef) ex.valueType();
  if (!cr) return null;
  auto cl = cr.myClass;
  
  string member;
  
  auto pre_ex = ex;
  if (t2.accept(".") && t2.gotIdentifier(member)) {
    auto m = cl.lookupRel(member, iparse!(Expr, "class_ptr_access", "tree.expr")("*cast(Cl*) hdl", "Cl", cl, "hdl", ex));
    text = t2;
    return m;
  } else return null;
}
mixin DefaultParser!(gotClassMemberExpr, "tree.rhs_partial.access_class_member");
