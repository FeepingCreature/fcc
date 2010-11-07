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
    if (i < 4) _lookupCM("start").jump();
  }
  
  auto forb = new Forble, garb = new Garble;
  writeln "Handlers: forb $(findHandler(forb)), garb $(findHandler(garb))";
  
  _CondMarker cm;
  cm.prev = _cm;
  cm.name = "start";
  if (_record) cm.guard_id = _record.dg;
  _cm = &cm;
  if setjmp _lookupCM("start").target
    writeln "Nonlocal entry. ";
  i++;
  writeln "$i";
  onExit writeln ("Failure guard called! ");
  callHandler(new Garble);
}
