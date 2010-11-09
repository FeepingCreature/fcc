module edp;

import sys, std.stream, std.string, std.file;

import std.c.unistd;

string slice(string* s, string marker) {
  string res;
  alias sref = *s;
  auto pos = find(sref, marker);
  if (pos == -1) {
    (res, sref) = (sref, string:(null, null));
  } else {
    (res, sref) = (sref[0 .. pos], sref[pos + marker.length .. sref.length]);
  }
  return res;
}

import std.c.poll, std.c.stdlib;
template process(T) <<EOF
  class ProcessorError { }
  class processor {
    T source;
    char[auto~] buffer;
    string[auto~] yieldbuf;
    bool done;
    int readTo(string marker) {
      int pos;
      do pos = find(buffer[], marker);
      while pos == -1 {
        byte[] sup;
        if (sup <- source) { buffer ~= char[]:sup; }
        else { done = true; return 0; }
      }
      return pos;
    }
    string step() {
      if (yieldbuf.length) {
        string res;
        (res, yieldbuf) = (yieldbuf[0], string[auto~]:yieldbuf[1 .. yieldbuf.length]);
        return res;
      }
      int startpos = readTo("<?exec ");
      if !startpos {
        string res;
        (res, buffer) = (buffer[], char[auto~]:new char[0]);
        return res;
      }
      int endpos = readTo("</exec>");
      if !endpos {
        writeln "No closing exec! ";
        raise-error (new ProcessorError);
      }
      string pre, main, post;
      (pre, main, post) = buffer[(0..startpos, startpos + 7 .. endpos, endpos + 7 .. buffer.length)];
      if (find(main, ">") == -1) {
        writeln "No > in \"$main\". ";
        raise-error (new ProcessorError);
      }
      auto cmd = slice(&main, ">");
      int[2] hdl_sysward, hdl_selfward;
      pipe(hdl_sysward); // self -> system()
      pipe(hdl_selfward); // system() -> self
      system(toStringz "exec $(hdl_sysward[1])>&-; exec $(hdl_selfward[0])>&-; <&$(hdl_sysward[0]) $cmd >&$(hdl_selfward[1]) &");
      close(hdl_sysward[0]); // read side
      close(hdl_selfward[1]); // write side
      char[auto~] newmain;
      bool running = true;
      int fdslength = 2;
      while running {
        pollfd[2] fds;
        fds[0].fd = hdl_selfward[0];
        fds[0].events = POLLIN;
        fds[1].fd = hdl_sysward[1];
        fds[1].events = POLLOUT;
        auto hits = poll(fds.ptr, fdslength, -1);
        if fds[0].revents & POLLHUP running = false;
        else {
          if fds[0].revents & POLLIN {
            char[128] buf;
            auto size = read(hdl_selfward[0], buf.ptr, buf.length);
            if (size > 0) {
              newmain ~= buf[0 .. size];
            }
          }
          if fds[1].revents & POLLOUT {
            auto res = write (hdl_sysward[1], main.ptr, main.length);
            if res < 0 {
              raise-error (new ProcessorError);
            }
            main = main[res .. main.length];
            if !main.length { close hdl_sysward[1]; fdslength = 1; }
          }
        }
      }
      yieldbuf ~= pre;
      yieldbuf ~= newmain[];
      buffer = char[auto~]:post;
      return step();
    }
    bool ivalid() { return eval !done; }
  }
  processor process(T src) using new processor {
    source = src;
    return this;
  }
EOF

import std.c.stdio;
extern(C) FILE* stdin;
void main() {
  auto stdin = readfile stdin; //, stdout = writefile 0;
  // stdout byte[]:"forble\n";
  char[auto~] res; string entry;
  while (entry <- process stdin) res ~= entry;
  writeln "$(res[])";
}
