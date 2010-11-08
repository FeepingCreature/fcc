module test3;

import sys, std.c.setjmp;

_Handler* findHandler(Object obj) {
  auto cur = _hdl;
  while cur {
    if cur.accepts(obj) return cur;
    cur = cur.prev;
  }
  return _Handler*:null;
  // writeln "No handler found to match $obj. ";
  // _interrupt 3;
}

void callHandler(Object obj) {
  findHandler(obj).dg(obj);
}

class Forble { }
class Garble : Forble { }

void main(int argc, char** argv) {
  int i;
  set-handler (Garble g) {
    // writeln "Garble handler; $i. ";
    if (i < 4) invoke-exit("start");
  }
  
  define-exit "start" {
    writeln "Nonlocal entry. ";
  }
  writeln "$(i++)";
  onExit writeln ("Failure guard called! ");
  callHandler(new Garble);
}
