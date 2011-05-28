module std.util;

template iterOnce(T) <<EOF
  class one {
    T t;
    bool done;
    T step() {
      done = true;
      return t;
    }
    bool ivalid() {
      return eval !done;
    }
  }
  one iterOnce(T t) {
    auto res = new one;
    res.t = t;
    return res;
  }
EOF
