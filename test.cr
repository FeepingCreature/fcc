module test;
import sys;

int add(int a, int b) { return a + b; }

void test(int foo) {
  int bar = 17;
  if (foo) writeln("meep");
  else writeln("moop");
  writeln("Hello World: $(foo * add(2, bar)), $bar");
  int temp = 5;
  while (temp) {
    writeln("Countdown with $temp");
    temp = temp - 1;
  }
  for (int x = 0; x < 10; ++x)
    writeln("Test: $x");
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
  writeln("meep $i, $k");
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
    writeln("Hello W; i = $i, i + 3 = $$test2(3)");
  }
}

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
extern(C) {
  SDL_Surface* SDL_SetVideoMode(int width, int height, int bpp, int flags);
  int SDL_Flip(SDL_Surface*);
  int usleep(int secs);
  int SDL_WaitEvent(SDL_Event*);
  int SDL_PollEvent(SDL_Event*);
  int rand();
}

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
  //                                                  SDL_ANYFORMAT
  SDL_Surface* surface = SDL_SetVideoMode(640, 480, 0, 268435456);
  int update() {
    SDL_Flip(surface);
    SDL_Event ev;
    while SDL_PollEvent(&ev) {
      if ev.type == 12 return 1; // QUIT
    }
    return 0;
  }
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
  }
  while 1 {
    usleep(64K);
    if update() return;
  }
}

interface IA {
  void iafun();
}

interface IB {
  void ibfun();
}

interface IC : IA, IB {
  void icfun();
}

interface ID {
  void idfun();
}

class Class {
  int i;
  void foo(int k) { writeln("foo $(k+i); btw this is $this"); }
  void bar() { writeln("bar here"); }
}

class Subclass : Class, IC, ID {
  int k;
  void iafun() { writeln("IA in Sub: this $this"); }
  void ibfun() { writeln("IB in Sub: this $this"); }
  void icfun() { writeln("IC in Sub: this $this"); }
  void idfun() { writeln("ID in Sub: this $this"); }
  void foo(int l) { writeln("subfoo $(i + k + l)"); }
}

void nesttest() {
  int nest_test = 13;
  void nestfun() { int a; a = 7; void nestfun2() { nest_test = a; } nestfun2(); }
  void delegate() nf = &nestfun;
  nf();
  writeln("nest test: $nest_test. ");
  int function(int, int x) fp = &s;
  writeln("s test $$fp(4, 5)");
}

struct Blarg {
  int ib;
  void fun() { writeln("$ib!"); }
}

template Blorg(T) <<EOT
  struct Blorg {
    T t;
  }
EOT

template FunTemp(T) <<EOT
  void FunTemp(T t) {
    writeln("T::$(t.stringof)");
  }
EOT

int globvar;

context ctest {
  int var;
}

int main(int argc, char** argv) {
  test(2);
  test(0);
  int e = 5;
  // writeln("a(3, 12) = $$acker(3, 12)");
  int* ptr = &e;
  *ptr = 7;
  X x;
  x.a = 5; x.b = 6; x.c = 3;
  writeln("expression alias! $$x.foo");
  Y y;
  y.x = x;
  y.x.c = 5;
  writeln("It's a $(y.x.c)!");
  writeln("yo .. $(x.a), $$(x.b), $(x.c)");
  writeln("pointer to e: $ptr. e: $(*ptr), also $(*&*&e).");
  int m = 5, n = 8;
  writeln("post inc test: $(m++), $(m++)");
  writeln("test: $$*(&m - 1)");
  if (s(0, 1) && s(1, 0) && s(2, 1)) writeln("yes"); else writeln("no");
  if (s(0, 1) && s(1, 0) && s(2, 1) || s(3, 1)) writeln("yes"); else writeln("no");
  int[5] ifield;
  ifield[3] = 15;
  writeln("field access $$ifield[3]");
  int* ip = &ifield[3];
  writeln("field access via ptr $$ip[0], oh btw $$ifield.length");
  // ifield.length = 8; // will fail
  // ztest().i = 5; // correctly doesn't work
  char[] arr = "foob";
  writeln("proper array test: $$arr.length, contents $arr");
  writeln("slice: $$arr[1 .. 4], via ptr $$arr.ptr[1 .. 4]");
  nesttest();
  W w;
  w.i = 5;
  w.test();
  writeln("And done. ");
  Class cl = new Class;
  writeln("class size is $$typeof(cl).sizeof; method is $$typeof(&cl.foo).stringof");
  writeln("forble $$(&cl.foo).stringof");
  writeln("class is at $$cast(void*) cl, i $$&(cl.i)");
  cl.i = 3;
  cl.foo(2);
  void delegate(int) dgx = &cl.foo;
  dgx(3);
  (&cl.foo)(4);
  auto sub = new Subclass, sup = cast(Class) sub;
  sup.foo(-5);
  writeln("sub is $$cast(void*) sub");
  sub.iafun();
  sub.ibfun();
  sub.icfun();
  sub.idfun();
  auto ia = cast(IA) (cast(void*) sub + int.sizeof * 3);
  ia.iafun();
  auto forb = cast(char[]) "test";
  Blarg blg;
  {
    Blarg lolz() { Blarg res; return res; }
    using blg::
    ib = 7;
    using lolz()::
    ib = 5;
  }
  blg.fun();
  do int i = rand() % 10; while (i) writeln("::$i");
  Blorg!int foo;
  writeln("template test: $$typeof(foo.t).stringof");
  FunTemp!int(5);
  globvar = 17;
  ctest.var = 17;
  using scoped ctest {
    writeln("var: $var");
    var = 14;
    writeln("now it's $var");
  }
  writeln("now back to $$ctest.var. ");
  void memtest() using sys.mem {
    writeln("memtest! ");
    auto p = malloc(16);
    free(p);
  }
  memtest();
  auto old_malloc = sys.mem.malloc_dg;
  using scoped sys.mem {
    void* fun(int i) {
      writeln("malloc($i)");
      return old_malloc(i);
    }
    malloc_dg = &fun;
    memtest();
  }
  memtest();
  auto testp = sys.mem.malloc(15);
  auto artest = new(3) int;
  artest[2] = 15;
  artest[0 .. 2] = artest[1 .. 3];
  writeln("test is $$artest.length, $$artest[1], $$artest[2]");
  writeln("Array test: $artest");
  {
    char[] s1 = "foo", s2 = "bar", s3 = s1 ~ s2;
    writeln("s3 is $s3, or $$s1 ~ s2, length $$s3.length");
  }
  atexit writeln("global is $globvar, $$&globvar, $$*&globvar");
  atexit writeln("Exit. ");
  atexit writeln("Exit 2. ");
  {
    atexit writeln("Exit 3. ");
    sdlfun();
    return 0;
    atexit writeln("Exit 4. ");
  }
}
