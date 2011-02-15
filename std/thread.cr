module std.thread;

c_include "pthread.h";
extern(C) int pthread_create(pthread_t*, pthread_attr_t*,
                             void* function(void*), void*);

void* start_routine(void* p) {
  (*void delegate()*:p)();
  return null;
}

void startThread(void delegate() dg) {
  pthread_t buf;
  auto argp = new void delegate();
  *argp = dg;
  pthread_create(&buf, null, &start_routine, argp);
}
