module test2;

import sys, std.file, std.string;

import std.c.sys.socket, std.c.sys.types, std.c.unistd, std.c.netdb;

class Socket {
  int sockfd;
  void close() {
    std.c.unistd.close(sockfd);
    sockfd = 0;
  }
  // alias isOpen = sockfd;
  void open(string dns, short port) {
    writeln "create fd";
    sockfd = socket (AF_INET, SOCK_STREAM, 0);
    writeln "lookup hostname";
    auto he = gethostbyname(toStringz(dns));
    sockaddr_in server;
    server.sin_addr.s_addr = *cast(uint*) he.h_addr_list[0];
    server.sin_family = AF_INET;
    server.sin_port = htons(port);
    writeln "connect";
    std.c.sys.socket.connect (sockfd, cast(sockaddr*) &server, typeof(server).sizeof);
    writeln "done";
  }
  int recv(void[] buf) {
    auto res = std.c.sys.socket.recv(sockfd, buf.ptr, buf.length, 0);
    if (res <= 0) {
      close;
    }
    return res;
  }
  int send(void[] buf) {
    auto res = std.c.sys.socket.send(sockfd, buf.ptr, buf.length, 0);
    if (res <= 0) {
      close;
    }
    return res;
  }
}

void main() {
  auto iter = [for 1 .. 4: 5];
  printf("iter is %i %i %i %i\n", iter);
  writeln("iter: $$typeof(iter).stringof");
  while (0..5)[2..5] writeln("foo");
  while int i <- [for 1..4: 5]
    writeln("$i");
  while int i <- [for 1..4: 6][2..3]
    writeln("$i");
  writeln("------");
  auto squares = [for k <- 0..10: k*k];
  writeln("$(squares.eval)");
  while auto line <- zip (0..-1, splitAt("\n", readfile open "parsers.txt"))
    writeln("$(line[0]): $(line[1])");
  auto sock = new Socket;
  sock.open("google.de", 80);
}
