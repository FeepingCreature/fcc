module test3;

import sys, std.c.setjmp;

struct Handler {
  Handler* prev;
  string name;
  jmp_buf target;
  void delegate() guard_id;
  void jump() {
    // TODO: pointer comparisons, dg comparisons
    if (!guard_id.fun) {
      while _record { _record.dg(); _record = _record.prev; }
    } else {
      while (_record.dg.fun != guard_id.fun) && (_record.dg.data != guard_id.data) {
        _record.dg();
        _record = _record.prev;
      }
    }
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
  if (_record) hdl.guard_id = _record.dg;
  _hdl = &hdl;
  int i;
  if setjmp lookupHdl("start").target
    writeln "Nonlocal entry. ";
  i++;
  writeln "$i";
  onExit writeln ("Failure guard called! ");
  if (i < 10) lookupHdl("start").jump();
}
