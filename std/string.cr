module std.string;

import sys;

int find(string text, string match) {
  for (int i = 0; i <= text.length - match.length; ++i) {
    if (text[i .. i+match.length] == match) return i;
  }
  return -1;
}

string startsWith(string s, string m) {
  if s.length < m.length return null;
  if (s[0 .. m.length] != m)
    return null;
  return s[m.length .. s.length];
}

string endsWith(string s, string m) {
  if s.length < m.length return null;
  if (s[$-m.length .. $] != m)
    return null;
  return s[0 .. $-m.length];
}

string between(string s, string from, string to) {
  int pos1, pos2;
  if (from.length) pos1 = find(s, from);
  if (pos1 == -1) return null;
  s = s[pos1 + from.length .. s.length];
  
  if (to.length) pos2 = find(s, to);
  if (pos2 == -1) return null;
  s = s[0 .. pos2];
  
  return s;
}

template join(T) <<EOF
  type-of __istep init!T join(T t) {
    type-of (__istep t)[0] [auto~] res;
    while auto chunk <- t { res ~= chunk; }
    return res[];
  }
EOF

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
      buffer = type-of buffer: buffer[pos + sup[0].length .. buffer.length];
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

string CToString(char* c) {
  char* cur = c;
  while (*cur) cur++;
  return c[0 .. (int:cur - int:c)];
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

template castIter(T) <<EOF
  template castIter(U) <<EO2
    class caster {
      U sup;
      T step() {
        return T: sup.step();
      }
      bool ivalid() { return sup.ivalid(); }
    }
    caster castIter(U u) {
      auto res = new caster;
      res.sup = u;
      return res;
    }
  EO2
EOF

// before, after
(string, string) slice(string s, string m) {
  auto pos = find(s, m);
  // if (pos == -1) return (s, string:null);
  if (pos == -1) {
    writeln "|$m| not found in |$s| for slice! ";
    _interrupt 3;
  }
  return (s[0 .. pos], s[pos + m.length .. s.length]);
}

string strip(string s) {
  alias first = s[0];
  alias last = s[s.length - 1];
  while s.length && (last == "\n"[0] || last == "\r"[0] || last == " "[0])
    s = s[0 .. s.length - 1];
  while s.length && (first == "\n"[0] || first == "\r"[0] || first == " "[0])
    s = s[1 .. s.length];
  return s;
}
