module test4;

import sys;

void main() {
  int x = 1, y = 2, x-z = 3;
  x-z = x-y;
  writeln "x-z = $x-z";
  if  (auto cond1 = delegate bool() { writeln "First. "; return false; }())
   && (auto cond2 = delegate bool() { writeln "Second. "; return true; }())
    writeln "Yay";
  else
    writeln "No-Yay";
}
