module std.boehm; // use Boehm GC

import c.gc, std.thread;

pragma(lib, "gc");

void* myDebugRealloc(void* a, size_t b) { return GC_debug_realloc(a, int:b, "", 0); }
void* myDebugMalloc(int a) { return GC_debug_malloc(int:a, "", 0); }
void* myDebugCalloc(int a, b) { return myDebugMalloc(a * b); }

void* myRealloc(void* a, size_t b) { return GC_realloc(a, int:b); }
void* myMalloc(int a) { return GC_malloc(int:a); }
void* myCalloc(int a, b) { return myMalloc(a * b); }

void register_thread() {
  GC_stack_base gsb;
  gsb.mem_base = stack-base;
  // writeln "register stack base $(stack-base) (ebp $(_ebp))";
  GC_register_my_thread(&gsb);
}

void initBoehm(bool debugMode = false) {
  (mem.malloc_dg, mem.calloc_dg, mem.realloc_dg, mem.free_dg)
    = [(&myMalloc,      &myCalloc,      &myRealloc,      &GC_free),
       (&myDebugMalloc, &myDebugCalloc, &myDebugRealloc, &GC_debug_free)
      ][debugMode];
  GC_init;
  GC_allow_register_threads;
  auto oldDg = onThreadCreation;
  onThreadCreation = new delegate void() {
    if (oldDg) oldDg();
    register_thread();
  };
}
