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
    bool done;
    // Expr yieldAdvance(LValue);
    string step() {
      int pos;
      do pos = find (buffer[], sup[0]);
      while pos == -1 {
        string supstep; // TODO: investigate why auto fails here.
        if (supstep <- sup[1]) { buffer ~= supstep; } else { done = true; return buffer[]; }
      }
      auto res = buffer[0 .. pos];
      buffer = typeof(buffer):buffer[pos + sup[0].length .. buffer.length];
      return res;
    }
    // Cond terminateCond(Expr); // false => can't yield more values
    bool ivalid() {
      return eval !done;
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
  auto s2 = new char[s.length + 1];
  s2[0 .. s.length] = s;
  s2[s.length] = ch;
  return s2.ptr;
}

string concat(string[] strs) {
  char[auto~] res;
  while auto str <- strs res ~= str;
  return res[];
}

import std.c.stdlib;
alias c_atoi = atoi;
alias c_atof = atof;

int atoi(string s) {
  auto p = toStringz(s);
  onExit mem.free(p);
  return c_atoi(p);
}

float atof(string s) {
  char* p = toStringz(s);
  onExit mem.free(p);
  return float:c_atof(p);
}
