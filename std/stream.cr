module std.stream;

import sys;

class iter {
  int delegate(void[]) dg;
  char[512] buffer;
  bool done;
  // Expr yieldAdvance(LValue);
  string step() {
    int pos = dg(cast(void[]) buffer);
    if pos == -1 {
      done = true;
      return cast(string) (null, null);
    }
    return buffer[0..pos];
  }
  // Cond terminateCond(Expr); // false => can't yield more values
  bool ivalid() {
    return eval !done;
  }
}

iter readDg(int delegate(void[]) dg) {
  auto res = new iter;
  res.dg = dg;
  return res;
}
