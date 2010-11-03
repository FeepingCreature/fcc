module hello;

import sys;

int helo(int a, int b) { return a + b; }

void main() {
  writeln("Hello World");
  writeln "The sum of numbers from 1 to 10 is $(sum 1..11). ";
  (int, int) forb;
  forb[0] = 15;
  (forb[1], forb[0]) = forb;
  writeln "15, 0 swapped is $forb. ";
}
