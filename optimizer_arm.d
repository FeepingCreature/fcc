module optimizer_arm;

import optimizer_base, ast.base;

bool armOptsSetup;
void setupARMOpts() {
  synchronized {
    if (armOptsSetup) return;
    armOptsSetup = true;
    mixin(opt("collapse_load_specific", `^Mov, ^Mov, (^Pop || ^Mov):
      $0.to == $1.from && $1.from.isRegister() && $1.to.isRegister()
      && (
        ($2.kind == $TK.Pop && $2.dest.find($0.to) != -1)
        ||
        ($2.kind == $TK.Mov && $2.from.startsWith("=") && $2.to.find($0.to) != -1)
      )
      =>
      $T t = $0;
      t.to = $1.to;
      $SUBST(t, $2);
    `));
    // hackaround
    mixin(opt("load_r1_later", `^Mov, ^Mov: $0.from.startsWith("=") && $1.from.startsWith("=") && $0.to == "r1" && $1.to == "r0"
      =>
      $SUBST($1, $0);
    `));
    mixin(opt("move_regload_down", `^Mov, ^Pop:
      $0.to.isRegister() && ($0.from.isRegister() || $0.from.startsWith("="))
      && !info($1).opContains($0.to) && (!$0.from.isRegister() || !info($1).opContains($0.from))
      =>
      $SUBST($1, $0);
    `));
    mixin(opt("direct_call", `^Mov, ^Call:
      $0.from.startsWith("=") && $0.to == $1.dest
      =>
      $T t = $1;
      t.dest = $0.from.startsWith("=");
      $SUBST(t);
    `));
  }
}
