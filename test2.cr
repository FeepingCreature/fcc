module test2;

import sys;

void main() {
  auto iter = [for 1 .. 4: 5];
  printf("iter is %i %i %i %i\n", iter);
  writeln("iter: $$typeof(iter).stringof");
  while (0..5)[1..5] writeln("foo");
  while int i <- [for 1..4: 5]
    writeln("$i");
  while int i <- [for 1..4: 6][2..3]
    writeln("$i");
  writeln("------");
  while int i <- [for k <- 0..10: k*k]
    writeln("$i");
}
