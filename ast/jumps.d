module ast.jumps;

import ast.base;

class Label : Statement {
  string name;
  override void emitAsm(AsmFile af) {
    af.emitLabel(name);
  }
}

class GotoStmt : Statement {
  string target;
  override void emitAsm(AsmFile af) {
    af.jump(target);
  }
}
