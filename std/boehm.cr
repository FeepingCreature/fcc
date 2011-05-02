module std.boehm; // use Boehm GC

import c.gc;

void* myCalloc(int a, b) {
  auto len = a * b;
  auto res = sys.mem.malloc(len);
  if !res return null;
  
  int fillLeft = len;
  auto ip = int*:res;
  while fillLeft >= 4 {
    *(ip++) = 0;
    fillLeft -= 4;
  }
  
  byte nil;
  auto bp = byte*:ip;
  while fillLeft-- *(bp++) = nil;
  
  return res;
}

void* myRealloc(void* a, size_t b) { return GC_realloc(a, int:b); }

void initBoehm() {
  mem.malloc_dg = &GC_malloc;
  mem.calloc_dg = &myCalloc;
  mem.realloc_dg = &myRealloc;
  mem.free_dg = &GC_free;
}
