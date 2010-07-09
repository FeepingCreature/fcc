module ast.oop;

class VTable {
  Stuple!(Delegate, string)[] funs;
  Delegate lookup(string name) {
    foreach (fun; funs)
      if (fun._1 == name) return fun._0;
  }
  int getOffset(Delegate dg) {
    foreach (i, fun; funs)
      if (fun._0 is dg) return i;
    assert(false);
  }
}

class Class : Namespace {
  VTable myfuns;
  Structure data;
}
