module test2;

import sys;

void main() {
  auto iter = [for 1 .. 4: 5];
  printf("iter is %i %i %i %i\n", iter);
  writeln("iter: $$typeof(iter).stringof");
  while 1..5 writeln("foo");
  while int i <- [for 1..4: 5]
    writeln("$i");
}
