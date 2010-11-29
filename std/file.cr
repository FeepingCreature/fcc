module std.file;

import sys, std.c.stdio, std.c.fcntl;

template readfile(T) <<EOF
  class reader {
    FILE* hdl;
    bool done;
    byte[256] buf;
    byte[] step() {
      auto size = fread(buf.ptr, 1, buf.length, hdl);
      if size <= 0 { done = true; return new byte[0]; }
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

import std.string;
FILE* open(string file) {
  auto ptr = toStringz(file);
  onExit mem.free(ptr);
  return fopen(ptr, "r");
}

ubyte[] readAll(string file) { return join readfile open file; }

class WriterError {
}

class writer {
  FILE* hdl;
  void step(byte[] data) {
    while data.length {
      auto res = fwrite(data.ptr, data.length, 1, hdl);
      if res < 0 raise-error (new WriterError);
      data = data[res .. data.length];
    }
  }
}

void delegate(byte[]) writefile(FILE* _hdl) using new writer {
  hdl = _hdl;
  return &step;
}
