module ast.oop;

class VTable {
  VTableData[] data;
  Delegate lookup(string name, Expr infoptr) {
    foreach (fun; data.funs)
      if (fun.name == name) {
        // TODO: embed micro env here, git pull
      }
  }
  int getOffset(Delegate dg) {
    foreach (i, fun; funs)
      if (fun._0 is dg) return i;
    assert(false);
  }
}

class VTableData {
  RelFunction[] funs;
  
}

class Class : Namespace, Named, IType {
  VTable myfuns;
  Structure data;
  string name;
  this(string name) {
    this.name = name;
    New(data, null);
    New(myfuns);
  }
  override {
    string gotIdentifier() {
      return name;
    }
    int size() { return data.size; }
    void _add(string name, Object obj) {
      if (auto rf = cast(RelFunction) obj) {
        myfuns.funs ~= 
      }
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
      namespace().add(st);
      text = t2;
      return Single!(NoOp);
    } else {
      throw new Exception("Couldn't match structure body at "~t2.next_text());
    }
  } else return null;
}
mixin DefaultParser!(gotStructDef, "tree.typedef.struct");
