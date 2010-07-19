module ast.oop;

import ast.parse, ast.base, ast.dg, ast.int_literal, ast.fun,
  ast.namespace, ast.structure, ast.structfuns, ast.pointer;

import tools.log;
class VTable {
  RelFunction[] funs;
  Function lookup(string name, Expr classptr) {
    logln("vtable lookup ", name, " in ", funs);
    foreach (id, fun; funs)
      if (fun.name == name) {
        return iparse!(Function, "vtable_lookup", "tree.expr")(
          "*(*cast(fntype**) classptr)[id].toDg(cast(void*)classptr)",
          "classptr", classptr,
          "id", new IntExpr(id),
          "fntype", fun.typeAsFp()
        );
      }
    return null;
  }
  int getOffset(Delegate dg) {
    foreach (i, fun; funs)
      if (fun == dg) return i;
    assert(false);
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

class Class : Namespace, RelNamespace, Named, IType {
  VTable myfuns;
  Structure data;
  string name;
  this(string name) {
    this.name = name;
    New(data, cast(string) null);
    New(myfuns);
    new RelMember("vtable", Single!(Pointer, Single!(Void)), this);
  }
  mixin TypeDefaults!();
  override {
    string getIdentifier() {
      return name;
    }
    int size() { return data.size(); }
    string mangle() { return "classdata_of_"~name; }
    void _add(string name, Object obj) {
      if (auto rf = cast(RelFunction) obj) {
        myfuns.funs ~= rf;
      } else {
        super._add(name, obj);
      }
    }
    string mangle(string name, IType type) {
      return "class_"~this.name~"_"~name~"_of_"~type.mangle();
    }
    Stuple!(IType, string, int)[] stackframe() {
      Stuple!(IType, string, int)[] res;
      select((string, RelMember rm) {
        res ~= stuple(rm.type, rm.name, rm.offset);
      });
      return res;
    }
    Object lookupRel(string str, Expr base) {
      if (auto res = sup.lookup(str, true)) {
        return cast(Object) res;
      }
      if (auto res = myfuns.lookup(str, base)) {
        return cast(Object) res;
      }
      return null;
    }
  }
}

// copypaste from ast/structure.d :(
Object gotClassDef(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("class ")) return null;
  string name;
  Class cl;
  if (t2.gotIdentifier(name) && t2.accept("{")) {
    New(cl, name);
    cl.sup = namespace();
    if (matchStructBody(t2, cl, cont, rest)) {
      if (!t2.accept("}"))
        throw new Exception("Missing closing bracket at "~t2.next_text());
      namespace().add(cl);
      logln("register class ", cl.name);
      text = t2;
      return Single!(NoOp);
    } else {
      throw new Exception("Couldn't match structure body at "~t2.next_text());
    }
  } else return null;
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
  
  // logln("match class member off ", t2.next_text());
  auto pre_ex = ex;
  if (t2.accept(".") && t2.gotIdentifier(member)) {
    logln("lookupRel on ", cl);
    auto m = cl.lookupRel(member, ex);
    logln("m is ", m);
    /*ex = cast(Expr) m;
    if (!ex) {
      if (m) throw new Exception(Format(member, " is not a class member: ", m));
      else throw new Exception(Format(member, " is not a member of class ", cl.name, "!"));
      return null;
    }
    text = t2;
    return cast(Object) ex;*/
    text = t2;
    return m;
  } else return null;
}
mixin DefaultParser!(gotClassMemberExpr, "tree.rhs_partial.access_class_member");
