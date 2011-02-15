module std.thread;

c_include "pthread.h";
extern(C) int pthread_create(pthread_t*, pthread_attr_t*,
                             void* function(void*), void*);

void __start_routine_unaligned(void delegate() dg) { dg(); }

void* __start_routine(void* p) {
  int[2] filler; // thread alignment; todo: make generic.
  __start_routine_unaligned (*void delegate()*:p);
  return null;
}

void startThread(void delegate() dg) {
  pthread_t buf;
  auto argp = new void delegate();
  *argp = dg;
  pthread_create(&buf, null, &__start_routine, argp);
}

struct pthread_mutex_t { ubyte[40] filler; }
extern(C) int pthread_mutex_lock (pthread_mutex_t*);
extern(C) int pthread_mutex_unlock (pthread_mutex_t*);

class Mutex {
  pthread_mutex_t mutex;
  void lock() { pthread_mutex_lock &mutex; }
  void unlock() { pthread_mutex_unlock &mutex; }
}

struct MutexWrapper {
  Mutex m;
  void onUsing() { m.lock(); }
  void onExit() { m.unlock(); }
}

MutexWrapper autoLock(Mutex m) { MutexWrapper mw; mw.m = m; return mw; }

c_include "semaphore.h";
class Semaphore {
  sem_t hdl;
  void init() { sem_init(&hdl, false, 0); }
  void claim() { sem_wait(&hdl); }
  void release() { sem_post(&hdl); }
}

class ThreadPool {
  Mutex m;
  Semaphore s, t;
  int tasksLeft;
  void delegate()[auto~] queue;
  void threadFun() {
    while (true) {
      s.claim;
      void delegate() dg;
      /*using autoLock m {
        writeln "got dg? ";
        dg = queue[0];
        queue = type-of queue:queue[1 .. $];
      }*/
      m.lock;
      dg = queue[0];
      queue = type-of queue:queue[1 .. $];
      m.unlock;
      dg();
      // using autoLock m { t.release(); }
      m.lock;
      t.release;
      m.unlock;
    }
  }
  void addThread() {
    startThread &threadFun;
  }
  void waitComplete() {
    int i;
    // using autoLock(m) { i = tasksLeft; tasksLeft = 0; }
    m.lock;
    i = tasksLeft;
    tasksLeft = 0;
    m.unlock;
    while 0..i t.claim();
  }
  void addTask(void delegate() dg) {
    using autoLock(m) { queue ~= dg; tasksLeft ++; s.release; }
    /*MutexWrapper mw; mw.m = m;
    eval (mw.onUsing);
    // m.lock;
    queue ~= dg;
    tasksLeft ++;
    s.release;
    eval (mw.onExit);
    // m.unlock;*/
    
  }
}

ThreadPool mkThreadPool(int threads = 0) using new ThreadPool {
  m = new Mutex;
  s = new Semaphore; t = new Semaphore;
  s.init; t.init;
  for 0..threads addThread();
  return this;
}
