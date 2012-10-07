module ast.jumps;

import ast.base;

class Label : Statement {
  string name;
  override void emitLLVM(LLVMFile lf) {
    lf.emitLabel(name, !keepRegs, !isForward);
  }
}

class GotoStmt : Statement {
  string target;
  override void emitLLVM(LLVMFile lf) {
    lf.jump(target);
  }
}
