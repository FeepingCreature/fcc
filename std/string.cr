module std.string;

import sys;

int find(string text, string match) {
  for (int i = 0; i <= text.length - match.length; ++i) {
    if (text[i .. i+match.length] == match) return i;
  }
  return -1;
}

template readlines(T) <<EOF
  struct iter {
    T sup;
    char[] buffer;
    // Expr yieldAdvance(LValue);
    string step() {
      int pos;
      do pos = find(buffer[], "\n");
      while pos == -1 {
        string supstep;
        if (supstep <- sup) { } else return new char[0];
        buffer ~= supstep;
      }
      auto res = buffer[0 .. pos];
      buffer = cast(typeof(buffer)) buffer[pos + 1 .. buffer.length];
      return res;
    }
    // Cond terminateCond(Expr); // false => can't yield more values
    bool ivalid() {
      return sup.ivalid();
    }
  }
  iter readlines(T t) {
    iter res;
    res.sup = t;
    return res;
  }
EOF

char* toStringz(string s) {
  char ch;
  s ~= (&ch)[0..1]; // lol
  return s.ptr;
}

string concat(string[] strs) {
  char[auto~] res;
  while auto str <- strs res ~= str;
  return res[];
}
