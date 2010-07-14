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
  alias foo = a+b*c;
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
  short pitch;
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

// 15.16
int fixedpoint_mult(int a, int b) {
  a = a / 256; // >> 8
  b = b / 256;
  return a * b;
}

struct ComplexI {
  int re, im;
}

ComplexI complex_mult(ComplexI a, ComplexI b) {
  ComplexI res;
  res.re = fixedpoint_mult(a.re, b.re) - fixedpoint_mult(a.im, b.im);
  res.im = fixedpoint_mult(a.re, b.im) + fixedpoint_mult(a.im, b.re);
  return res;
}

ComplexI complex_add(ComplexI a, ComplexI b) {
  ComplexI res;
  res.re = a.re + b.re;
  res.im = a.im + b.im;
  return res;
}

int lensq(ComplexI c) {
  return fixedpoint_mult(c.re, c.re) + fixedpoint_mult(c.im, c.im);
}

int num_to_fp(int i) {
  return i * 65536;
}

void sdlfun() {
  SDL_Init(32); // video
  SDL_Surface* surface = SDL_SetVideoMode(640, 480, 32, 0);
  for (int y = 0; y < surface.h; ++y) {
    for (int x = 0; x < surface.w; ++x) {
      ComplexI c;
      ComplexI p;
      c.re = num_to_fp(x - surface.w / 2) / 200;
      c.im = num_to_fp(y - surface.h / 2) / 200;
      p = c;
      int exceeded = 0;
      for (int i = 0; i < 64; ++i) {
        p = complex_add(complex_mult(p, p), c);
        if (lensq(p) > num_to_fp(2)) {
          exceeded = i;
          i = 64;
        }
      }
      int expix = exceeded * 8;
      expix = expix + expix * 256 + expix * 2 * 65536;
      if (exceeded)
        surface.pixels[y * surface.w + x] = expix;
      else
        surface.pixels[y * surface.w + x] = 0;
    }
    SDL_Flip(surface);
    SDL_Event ev;
    while SDL_PollEvent(&ev) {
      if ev.type == 12 return; // QUIT
    }
  }
}

/*class Class {
  int i;
  void foo() { }
}*/

void nesttest() {
  int nest_test = 13;
  void nestfun() { int a; a = 7; void nestfun2() { nest_test = a; } nestfun2(); }
  void delegate() nf = &nestfun;
  nf();
  printf("nest test: %i. \n", nest_test);
  int function(int, int x) fp = &s;
  printf("s test %i\n", fp(4, 5));
}

int main(int argc, char** argv) {
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
  printf("expression alias! %i\n", x.foo);
  Y y;
  y.x = x;
  y.x.c = 5;
  printf("It's a %i! \n", y.x.c);
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
  nesttest();
  W w;
  w.i = 5;
  w.test();
  printf("And done. \n");
  // Class cl;
  sdlfun();
}
