module threads;

import std.thread;

void main() {
  for (int i <- 0..10) 
    startThread new delegate void() { writeln "$i"; };
  while (true) { }
}
