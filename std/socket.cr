module std.socket;

import std.string, std.c.unistd, std.c.sys.socket, std.c.netdb;

class Address {
}

class TcpAddress : Address {
  sockaddr_in saddr;
}

TcpAddress tcpAddress(string dns, short port) using new TcpAddress {
  auto he = gethostbyname(toStringz(dns));
  using saddr {
    sin_addr.s_addr = * uint*:he.h_addr_list[0];
    sin_family = AF_INET;
    sin_port = htons(port);
  }
  return this;
}

class Socket {
  int sockfd;
  void close() {
    std.c.unistd.close(sockfd);
    sockfd = 0;
  }
  // alias isOpen = sockfd;
  void open(TcpAddress ta) {
    sockfd = socket (AF_INET, SOCK_STREAM, 0);
    auto res = std.c.sys.socket.connect (sockfd, sockaddr*:&ta.saddr, size-of type-of ta.saddr);
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
  void sendAll(void[] buf) {
    while buf.length {
      auto res = send buf;
      if (res <= 0) return;
      buf = buf[res .. $];
    }
  }
  void bind(Address addr) {
    _interrupt 3;
  }
  void listen(int backlog) {
    std.c.sys.socket.listen(sockfd, backlog);
  }
}
