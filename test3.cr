module test3;

import sys, std.c.setjmp;

void main(int argc, char** argv) {
  _CondMarker cm;
  cm.prev = _cm;
  cm.name = "start";
  if (_record) cm.guard_id = _record.dg;
  _cm = &cm;
  int i;
  if setjmp _lookupCM("start").target
    writeln "Nonlocal entry. ";
  i++;
  writeln "$i";
  onExit writeln ("Failure guard called! ");
  if (i < 10) _lookupCM("start").jump();
}
