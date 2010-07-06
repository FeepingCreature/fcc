module test;
import sys;

int add(int a, int b) { return a + b; }

void test(int foo) {
  int bar = 17;
  if (foo) sys.printf("meep\n");
  else sys.printf("moop\n");
  sys.printf("Hello World: %i, %i\n", foo * add(2, bar), bar);
  int temp = 5;
  while (temp) {
    sys.printf("Countdown with %i\n", temp);
    temp = temp - 1;
  }
  for (int x = 0; x < 10; ++x)
    sys.printf("Test: %i\n", x);
}

int acker(int m, int n) {
  if (m) {
    if (n) return acker(m - 1, acker(m, n - 1));
    else return acker(m - 1, 1);
  } else return n + 1;
}

struct X {
  int a, b;
  int c;
}

struct Y {
  X x;
  int i;
}

int s(int i, int k) {
  printf("meep %i: %i\n", i, k);
  return k;
}

struct Z {
  int i;
}

Z ztest() { Z z; z.i = 5; return z; }

struct W {
  int i;
  int test2(int k) { return i + k; }
  void test() {
    printf("Hello W; i = %i, i + 3 = %i\n", i, test2(3));
  }
}

extern(C) void* malloc(int);
extern(C) int SDL_Init(int);
struct SDL_Surface {
  int flags;
  void* format;
  int w, h;
  short pitch, alignfill;
  int* pixels;
}
struct SDL_Event {
  char type;
  int[64] filler;
}
extern(C) SDL_Surface* SDL_SetVideoMode(int width, int height, int bpp, int flags);
extern(C) int SDL_Flip(SDL_Surface*);
extern(C) int usleep(int secs);
extern(C) int SDL_WaitEvent(SDL_Event*);
extern(C) int SDL_PollEvent(SDL_Event*);
extern(C) int rand();
void sdlfun() {
  SDL_Init(32); // video
  SDL_Surface* surface = SDL_SetVideoMode(640, 480, 32, 0);
  for (int k = 0; k < (*surface).h; ++k)
    for (int i = 0; i < (*surface).w; ++i)
      (*surface).pixels[k * (*surface).w + i] = rand();
  SDL_Flip(surface);
  SDL_Event ev;
  printf("Event loop! \n");
  while 1 if SDL_PollEvent(&ev)
    if ev.type == 12 return; // QUIT
    else SDL_WaitEvent(cast(SDL_Event*) 0);
}

void main() {
  /*A a = new A;
  a.x = 5;
  test2(a);*/
  test(2);
  test(0);
  int e = 5;
  // printf("a(3, 12) = %i\n", acker(3, 12));
  int* ptr = &e;
  *ptr = 7;
  X x;
  x.a = 5; x.b = 6; x.c = 3;
  Y y;
  y.x = x;
  y.x.c = 5;
  printf("It's a %i! ", y.x.c);
  printf("yo .. %i, %i, %i\n", x.a, x.b, x.c);
  printf("pointer to e: %p. e: %i, also %i.\n", ptr, *ptr, *&*&e);
  int m = 5;
  int n = 8;
  printf("post inc test: %i, %i\n", m++, m++);
  printf("test: %i\n", *(&m - 1));
  if (s(0, 1) && s(1, 0) && s(2, 1)) printf("yes\n"); else printf("no\n");
  if (s(0, 1) && s(1, 0) && s(2, 1) || s(3, 1)) printf("yes\n"); else printf("no\n");
  int[5] ifield;
  ifield[3] = 15;
  printf("field access %i\n", ifield[3]);
  int* ip = &ifield[3];
  printf("field access via ptr %i, oh btw %i\n", ip[0], ifield.length);
  // ifield.length = 8; // will fail
  // ztest().i = 5; // correctly doesn't work
  char[] arr = "foob";
  printf("proper array test: %i; contents %.*s\n", arr.length, arr);
  printf("slice: %.*s, via ptr: %.*s\n", arr[1 .. 4], arr.ptr[1 .. 4]);
  int nest_test = 13;
  void nestfun() { int a; a = 7; void nestfun2() { nest_test = a; } nestfun2(); }
  void delegate() nf = &nestfun; nf();
  printf("nest test: %i. \n", nest_test);
  int function(int, int x) fp = &s;
  printf("s test %i\n", fp(4, 5));
  W w;
  w.i = 5;
  w.test();
  printf("And done. \n");
  sdlfun();
}
