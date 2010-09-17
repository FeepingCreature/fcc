module std.string;

import sys;

int find(string text, string match) {
  for (int i = 0; i <= text.length - match.length; ++i) {
    if (text[i .. i+match.length] == match) return i;
  }
  return -1;
}

template splitAt(T) <<EOF
  class iter {
    T sup;
    char[auto~] buffer;
    // Expr yieldAdvance(LValue);
    string step() {
      int pos;
      do pos = find(buffer[], sup[0]);
      while pos == -1 {
        string supstep;
        if (supstep <- sup[1]) { } else return new char[0];
        buffer ~= supstep;
      }
      auto res = buffer[0 .. pos];
      buffer = cast(typeof(buffer)) buffer[pos + 1 .. buffer.length];
      return res;
    }
    // Cond terminateCond(Expr); // false => can't yield more values
    bool ivalid() {
      return sup[1].ivalid();
    }
  }
  iter splitAt(T t) {
    auto res = new iter;
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
