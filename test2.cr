module test2;

import sys;

void main() {
  auto iter = [for 1 .. 4: 5];
  printf("iter is %i %i %i %i\n", iter);
  writeln("iter: $$typeof(iter).stringof");
  while (0..5)[1..5] writeln("foo");
  while int i <- [for 1..4: 5]
    writeln("$i");
  auto foo = [for 1..4: 6];
  printf("::  %i %i %i %i\n", foo);
  auto bar = foo[2..3];
  printf("::: %i %i %i %i\n", bar);
  // while int i <- [for 1..4: 6][2..3]
  //   writeln("$i");
}
