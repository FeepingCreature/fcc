module test2;

import sys, std.file, std.string, std.socket, std.stream;

void main() {
  auto iter = [for 1 .. 4: 5];
  printf("iter is %i %i %i %i\n", iter);
  writeln("iter: $$string-of type-of iter");
  while (0..5)[2..5] writeln("foo");
  while int i <- [for 1..4: 5]
    writeln("$i");
  while int i <- [for 1..4: 6][2..3]
    writeln("$i");
  writeln("------");
  auto squares = [for k <- 0..10: k*k];
  writeln("$(squares.eval)");
  while auto line <- zip (0..-1, splitAt("\n", castIter!string readfile open "parsers.txt"))
    writeln "$(line[0]): $(line[1])";
  auto foo = new int[4];
  foo[0] = 1000;
  writeln "$(byte[]:foo)";
  auto sock = new Socket;
  sock.open tcpAddress ("google.de", 80);
  sock.send void[]:"GET / HTTP/1.0\r\n\r\n";
  auto iter2 = splitAt ("\r\n", castIter!string readDg &sock.recv);
  writeln "$(iter2.eval)";
}
