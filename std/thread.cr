module std.thread;

c_include "pthread.h";
extern(C) int pthread_create(pthread_t*, pthread_attr_t*,
                             void* function(void*), void*);

void __start_routine_unaligned(void delegate() dg) { dg(); }

void* __start_routine(void* p) {
  void* ptemp = p; // will be top of the stack, so ..
  asm "popl %eax";
  asm "movl %esp, %ebx";
  asm `andl $0xfffffff0, %esp`;
  asm "pushl %ebx";
  asm "pushl %ebp";
  asm "pushl %eax";
  asm "movl %esp, %ebp";
  asm `subl $4, %ebp`;
  {
    alias arg = *(void delegate(), void*)*:ptemp;
    int[1] filler; // thread alignment; todo: make generic.
    _esi = arg[1];
    __start_routine_unaligned (arg[0]);
  }
  // and undo
  asm `addl $4, %esp`; // undo pushl %eax
  asm "popl %ebp";
  asm "popl %ebx";
  asm "movl %ebx, %esp";
  asm `pushl $0`; // undo popl %eax; pointer not needed anymore.
  return null;
}

extern(C) int[0] _sys_tls_data_start;
void startThread(void delegate() dg) {
  pthread_t buf;
  auto argp = new (void delegate(), void*);
  (*argp)[0] = dg;
  int dataStart = 0x7fffffff, dataEnd;
  auto
    localStart = [for mod <- __modules: int:mod.dataStart - int:&_sys_tls_data_start],
    localEnd = [for mod <- __modules: int:mod.dataEnd - int:&_sys_tls_data_start],
    localRange = zip(localStart, localEnd);
  for (auto tup <- zip(__modules, localRange)) {
    alias mod = tup[0], range = tup[1];
    if (range[0] < dataStart) dataStart = range[0];
    if (range[1] > dataEnd) dataEnd = range[1];
  }
  alias dataSize = dataEnd - dataStart;
  auto oldArea = _esi[dataStart..dataEnd];
  auto newArea = (sys.malloc(dataSize) - dataStart)[0 .. dataEnd];
  for (auto range <- localRange) {
    newArea[range[0] .. range[1]] = _esi[range[0] .. range[1]];
  }
  (*argp)[1] = newArea.ptr;
  
  pthread_create(&buf, null, &__start_routine, argp);
}

/*
struct pthread_mutex_t { ubyte[40] filler; }
extern(C) int pthread_mutex_init (pthread_mutex_t*, void*);
extern(C) int pthread_mutex_lock (pthread_mutex_t*);
extern(C) int pthread_mutex_unlock (pthread_mutex_t*);
*/

class Mutex {
  pthread_mutex_t mutex;
  void init() { pthread_mutex_init (&mutex, null); }
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
    if (int:_ebp & 0xf) {
      writeln "FEEEP! YOU BROKE THE FUCKING THREAD FRAME ALIGNMENT AGAIN. $(_ebp) ";
      _interrupt 3;
    }
    while (true) {
      s.claim;
      void delegate() dg;
      using autoLock m {
        dg = queue[0];
        queue = type-of queue:queue[1 .. $];
      }
      dg();
      using autoLock m { t.release(); }
    }
  }
  void addThread() {
    startThread &threadFun;
  }
  void waitComplete() {
    int i;
    using autoLock(m) { i = tasksLeft; tasksLeft = 0; }
    while 0..i t.claim();
  }
  void addTask(void delegate() dg) {
    using autoLock(m) { queue ~= dg; tasksLeft ++; s.release; }
  }
}

ThreadPool mkThreadPool(int threads = 0) using new ThreadPool {
  m = new Mutex;
  s = new Semaphore; t = new Semaphore;
  m.init;
  s.init; t.init;
  for 0..threads addThread();
  return this;
}
