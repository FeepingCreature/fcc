module std.time;

import std.c.time;

struct timeval {
  int tv_sec, tv_usec;
}
extern(C) int gettimeofday(timeval*, void*);
extern(C) int usleep(int); // I hope this really is int.

long µsec() {
  timeval tv;
  gettimeofday(&tv, null);
  return tv.tv_sec * long:1_000_000 + tv.tv_usec;
}

double sec() { return double:µsec() / 1_000_000; }

void sleep(float length) {
  usleep int:(length * 1_000_000);
}
