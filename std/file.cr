module std.file;

import c.stdio, c.fcntl, c.unistd;

template readfile(T) <<EOF
  class reader {
    int fd;
    bool done;
    byte x 256  buf;
    byte[] step() {
      auto size = read(fd, buf.ptr, buf.length);
      if size <= 0 { done = true; return new byte[] 0; }
      return buf[0 .. size];
    }
    bool ivalid() {
      return eval !done;
    }
  }
  reader readfile(T t) {
    auto res = new reader;
    res.fd = t;
    return res;
  }
EOF

alias C_open = open;

import std.string;

platform(default) <<EOF
  alias read-mode = O_RDONLY;
EOF

platform(i686-mingw32) <<EOF
  alias read-mode = O_RDONLY | O_BINARY; // FUCK YOU SO HARD MICROSOFT WINDOWS.
EOF

int open(string file) {
  auto ptr = toStringz(file);
  onExit mem.free(ptr);
  return C_open(ptr, read-mode);
}

ubyte[] readAll(string file) { return join readfile open file; }

class WriterError : Error {
  void init() { super.init "Writer Error"; }
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
  auto buffer = new char[] 128;
  while true {
    if (c_getcwd(buffer.ptr, buffer.length)) {
      return buffer[0 .. strlen buffer.ptr];
    }
    auto oldlen = buffer.length;
    buffer.free;
    buffer = new char[] (oldlen * 2);
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
