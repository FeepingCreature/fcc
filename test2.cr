module test2;

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

template forble(T) <<EOF
  struct forb {
    T sup;
    int step() {
      return sup[0]++;
    }
    bool ivalid() {
      return eval sup[0] != sup[1];
    }
  }
  forb forble(T t) {
    forb res;
    res.sup = t;
    return res;
  }
EOF

c_include "fcntl.h";
c_include "unistd.h";
template readfile(T) <<EOF
  struct reader {
    int hdl;
    bool done;
    string step() {
      auto buf = new char[256];
      auto size = read(hdl, buf.ptr, buf.length);
      if size <= 0 { done = true; return new char[0]; }
      return buf[0 .. size];
    }
    bool ivalid() {
      return eval !done;
    }
  }
  reader readfile(T t) {
    reader res;
    res.hdl = t;
    return res;
  }
EOF

char* toStringz(string s) {
  char ch;
  s ~= (&ch)[0..1]; // lol
  return s.ptr;
}

int my_open(string file) {
  auto ptr = toStringz(file);
  atexit mem.free(ptr);
  return open(ptr, O_RDONLY);
}

string concat(string[] strs) {
  char[auto~] res;
  while auto str <- strs res ~= str;
  return res[];
}

void main() {
  auto iter = [for 1 .. 4: 5];
  printf("iter is %i %i %i %i\n", iter);
  writeln("iter: $$typeof(iter).stringof");
  while (0..5)[2..5] writeln("foo");
  while int i <- [for 1..4: 5]
    writeln("$i");
  while int i <- [for 1..4: 6][2..3]
    writeln("$i");
  writeln("------");
  auto squares = [for k <- 0..10: k*k];
  writeln("$(squares.eval)");
  writeln("forble test: $(forble(0, 23).eval)");
  while auto line <- zip (0..-1, readlines readfile my_open "parsers.txt")
    writeln("$(line[0]): $(line[1])");
}
