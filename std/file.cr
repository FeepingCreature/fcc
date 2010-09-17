module std.file;

import sys, std.c.unistd, std.c.fcntl;

template readfile(T) <<EOF
  class reader {
    int hdl;
    bool done;
    char[256] buf;
    string step() {
      auto size = read(hdl, buf.ptr, buf.length);
      if size <= 0 { done = true; return new char[0]; }
      return buf[0 .. size];
    }
    bool ivalid() {
      return eval !done;
    }
  }
  reader readfile(T t) {
    auto res = new reader;
    res.hdl = t;
    return res;
  }
EOF

alias c_open = open;

import std.string;
int open(string file) {
  auto ptr = toStringz(file);
  atexit mem.free(ptr);
  return c_open(ptr, O_RDONLY);
}
