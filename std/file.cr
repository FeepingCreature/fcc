module std.file;

import sys, std.c.stdio, std.c.fcntl, std.c.unistd;

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

alias c_getcwd = getcwd;

string getcwd() {
  auto buffer = new char[128];
  while true {
    if (c_getcwd(buffer.ptr, buffer.length)) {
      return buffer[0 .. strlen buffer.ptr];
    }
    auto oldlen = buffer.length;
    buffer.free;
    buffer = new char[oldlen * 2];
  }
}

string basedir(string file) {
  if file.endsWith "/" return file;
  while file.length && file[$-1] != "/"[0]
    file = file[0 .. $-1];
  return file;
}

// in path1, access path2
string sub(string path1, path2) {
  if path2.startsWith "/" return path2;
  if path1.endsWith "/" return path1 ~ path2;
  return path1 ~ "/" ~ path2;
}
