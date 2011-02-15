module threads;

import std.thread;

void main() {
  auto tp = mkThreadPool(4);
  for (int i <- 0..10) 
    tp.addTask new delegate void() { writeln "$i"; };
  tp.waitComplete;
}
