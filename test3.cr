module test3;

import sys, std.c.setjmp;

struct Handler {
  Handler* prev;
  string name;
  jmp_buf target;
  void jump() {
    longjmp (target, 1);
  }
}

Handler* _hdl;

Handler* lookupHdl(string s) {
  auto cur = _hdl;
  while (cur) {
    if (cur.name == s) return cur;
    cur = cur.prev;
  }
  return Handler*:null;
}

void main(int argc, char** argv) {
  Handler hdl;
  hdl.prev = _hdl;
  hdl.name = "start";
  _hdl = &hdl;
  int i;
  if setjmp lookupHdl("start").target
    writeln "Nonlocal entry. ";
  i++;
  writeln "$i";
  if (i < 10) lookupHdl("start").jump();
}
