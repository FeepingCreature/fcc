module std.stream;

class iter {
  int delegate(void[]) dg;
  char x 512 buffer;
  bool done;
  // Expr yieldAdvance(LValue);
  string step() {
    int pos = dg(void[]:buffer);
    if pos == -1 {
      done = true;
      return null;
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

template dgIter(T) <<EOF
  class DelegateIterator {
    T t;
    alias dg = t;
    type-of dg() step() { return dg(); }
    bool ivalid() { return true; }
  }
  auto dgIter(T t) {
    auto res = new DelegateIterator;
    res.t = t;
    return res;
  }
EOF
