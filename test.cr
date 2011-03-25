module test;
import sdl, simplex, std.thread;

int delegate(int b) add(int a) { return new delegate int(int b) { return a + b; }; }

void test(int foo) {
  int bar = 17;
  if (foo) writeln("meep");
  else writeln("moop");
  writeln("Hello World: $(foo * add a=>2 b=>bar), $bar");
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

import std.c.math, std.c.fenv, std.c.unistd, std.c.stdlib, std.c.time;

void sdlfun(vec3f delegate(float, float, float) dg) {
  SDL_Init(32); // video
  SDL_Surface* surface = SDL_Surface*: SDL_SetVideoMode(256, 192, 32, SDL_ANYFORMAT);
  int update() {
    SDL_Flip(surface);
    SDL_Event ev;
    while SDL_PollEvent(&ev) {
      if ev.type == 12 return 1; // QUIT
    }
    return 0;
  }
  auto start = time(int*: null);
  float t = 0;
  int fps;
  auto tp = new ThreadPool(4);
  void run() {
    t += 0.02;
    void calc(int from, int to) {
      int factor1 = 0xff0000, factor2 = 0xff00, factor3 = 0xff;
      vec3f ff = vec3f(factor1, factor2, factor3);
      for (int y = from; y < to; ++y) {
        auto p = &((int*:surface.pixels)[y * int:surface.w]);
        vec3f f = void;
        vec3i i = void;
        for (int x = 0; x < surface.w; ++x) {
          f = dg(float:x / surface.w, float:y / surface.h, t) * ff;
          fastfloor3f (f, &i);
          *(p++) = i.x & factor1 + i.y & factor2 + i.z & factor3;
        }
      }
    }
    for (int i <- 0..8) {
      auto step = surface.h / 8;
      auto from = step * i, to = step * (i + 1);
      void delegate() myApply(int from, int to, void delegate(int, int) dg) {
        return new delegate void() { return dg(from, to); };
      }
      // myApply(from, to, &calc)();
      tp.addTask myApply(from, to, &calc);
    }
    tp.waitComplete;
    fps ++;
  }
  auto last = time(int*:null);
  while 1 {
    run();
    if (update()) return;
    if (auto tvar = time(null)) > last {
      last = tvar;
      writeln("FPS: $fps");
      fps = 0;
    }
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
    writeln("T::$(string-of t)");
  }
EOT

int globvar;

context ctest {
  int var;
}

union U {
  int I;
  float F;
}

// c_include "gc.h";

int main(string[] args) {
  mxcsr |= (1 << 6) | (3 << 13); // Denormals Are Zero; Round To Zero.
  // use Boehm GC
  /* mem.malloc_dg = &GC_malloc;
  void* myCalloc(int a, b) {
    auto len = a * b;
    auto res = sys.mem.malloc(len);
    char ch;
    (char*:res)[0 .. len] = [for 0..len: ch];
    return res;
  }
  void* myRealloc(void* a, size_t b) { return GC_realloc(a, int:b); }
  mem.calloc_dg = &myCalloc;
  mem.realloc_dg = &myRealloc;
  mem.free_dg = &GC_free;*/
  if (int:_ebp & 0xf) {
    writeln "FEEEP! YOU BROKE THE FUCKING FRAME ALIGNMENT AGAIN. $(_ebp) ";
    _interrupt 3;
  }
  auto cdg = mem.calloc_dg;
  mem.calloc_dg = delegate void*(int a, b) {
    // printf("Allocate %i, %i\n", a, b);
    if (a*b > 65536) {
      printf("Excessive allocation: %i, %i\n", a, b);
      _interrupt 3;
    }
    return cdg(a, b);
  };
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
  writeln("class size is $$size-of type-of cl; method is $$string-of type-of &cl.foo");
  writeln("forble $$string-of &cl.foo");
  writeln("class is at $$void*:cl, i $$&(cl.i)");
  cl.i = 3;
  cl.foo(2);
  void delegate(int) dgx = &cl.foo;
  dgx(3);
  (&cl.foo)(4);
  writeln "Alloc subclass. ";
  auto sub = new Subclass;
  writeln "Do sup cast";
  auto sup = Class:sub;
  writeln("sup is $$void*:sup");
  sup.foo(-5);
  writeln("sub is $$void*:sub");
  sub.iafun();
  sub.ibfun();
  sub.icfun();
  sub.idfun();
  IA ia = sub;
  writeln "call ia on implicit IA cast from sub; ia is $(void*:ia), sub is $(void*:sub), iafun is $(&ia.iafun), on sub would be $(&sub.iafun). ";
  ia.iafun();
  auto ic = IC:ia;
  ic.icfun();
  auto forb = char[]:"test";
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
  writeln("template test: $$string-of type-of foo.t");
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
    writeln("again.. ");
  }
  memtest();
  auto old_malloc = sys.mem.malloc_dg;
  using scoped sys.mem {
    void* fun(int i) {
      writeln("malloc()");
      return old_malloc(i);
    }
    malloc_dg = &fun;
    memtest();
  }
  memtest();
  auto testp = sys.mem.malloc(15);
  auto artest = new int[3];
  artest[2] = 15;
  artest[0 .. 2] = artest[1 .. 3];
  writeln("test is $$artest.length, $$artest[1], $$artest[2]");
  writeln("Array test: $artest");
  {
    char[] s1 = "foo", s2 = "bar", s3 = s1 ~ s2;
    writeln("s3 is $s3, or $$s1 ~ s2, length $$s3.length");
  }
  onExit writeln("global is $globvar, $$&globvar, $$*&globvar");
  onExit writeln("Exit. ");
  onExit writeln("Exit 2. ");
  float fl = 2;
  fl = fl + 10;
  writeln("fl is $fl");
  void testfl(float cmp) {
    if (fl > cmp) writeln("fl > $cmp");
    if (fl < cmp) writeln("fl < $cmp");
    if (fl == cmp) writeln("fl == $cmp");
  }
  testfl(11);
  testfl(12);
  testfl(13);
  {
    onExit writeln("Exit 3. ");
    float clamp(float from, float to, float f) {
      if (f <= from) return from;
      if (f >= to) return to;
      return f;
    }
    // http://en.wikipedia.org/wiki/Smoothstep
    float smoothstep(float edge0, float edge1, float x) {
      float old_x = x;
      x = (x - edge0) / (edge1 - edge0);
      if (x <= 0) return 0;
      if (x >= 1) return 1;
      return x * x * (3 - 2 * x);
    }
    vec3f transition(vec3f* a, vec3f* b, float f) {
      return (*a) * (1 - f) + (*b) * f;
    }
    float PI = 3.1415926538;
    float fun1(float x, float y) {
      float rx = 2 * (x - 0.5) * 1.333;
      float ry = 2 * (y - 0.5);
      float h = 3 * sqrtf(x*x*x);
      h = h * (1 - x);
      float e = fabsf(ry) - h;
      float f = smoothstep(0, 0.01, e);
      return f;
    }
    vec3f fun2(float x, float y) {
      x = x - 0.5;
      y = y - 0.5;
      float f = fun1(x + 0.5, y + 0.5);
      float angle = 15 * PI / 180.0;
      for (int i = 0; i < 24; ++i) {
        float x2 = x * cosf(angle) - y * sinf(angle);
        float y2 = y * cosf(angle) + x * sinf(angle);
        x = x2; y = y2;
        f = f * 0.8 + 0.2 * fun1(x + 0.5, y + 0.5);
      }
      return vec3f(f);
    }
    vec3f fun4(float x, float y, float t) {
      float factor = 1;
      float mew = noise3 vec3f(x * 2 + noise3 vec3f(-x*3, y*3, t/4), y * 2 + noise3 vec3f(x*3, -y*3, t/4), t);
      auto noise = (mew + 1) * 20;
      if (noise >= 30) factor = mew;
      
      noise -= int:noise;
      
      // Octave 2: Fine noise
      noise += noise3 vec3f(x * 200, y * 200, t) * 0.5;

      // Octave 3: Streak
      noise += noise3 vec3f(x, y * 100, t) * 0.7;

      // Adjust range to [0, 1]
      noise = (noise + 1) / 2;

      // Convert noise to colour
      auto res = vec3f(noise * 0.7, noise * 0.507, noise * 0.313);
      res *= factor;
      for (int i <- 0..3) res[i] = clamp(0, 1, res[i]);
      return res;
    }
    vec3f fun3(float x, float y, float t) {
      // auto f2 = fun2(x, y);
      x = x - 0.5f;
      y = y - 0.5f;
      // auto dist = sqrtf(x * x + y * y);
      // auto n = 0.5 * noise2(x * 4 + t, y * 4) + 0.25 * noise2(x * 8, x * 8 + t) + 0.125 * noise2(y * 16 + t, y * 16 + t) + 0.0625 * noise2(x * 32 + t, y * 32 - t * 2);
      // auto n = 0.5 * noise3 ((vec3f(x * 4, y * 4, sin(t) * 4)).zxy) + 0.25;
      float noisex(vec3f v) {
        float sqr(float f) { return f * f; }
        // return noise3 vec3f(v.x + sqr noise3(v), v.y + sqr noise3(-v), v.z);
        return noise3 v;
        // return sinf(v.x + v.y + v.z) * 0.5 + 0.5;
      }
      // auto n = noisex vec3f(x * 8, y * 8, t);
      
      /*auto res =
              0.5    * noisex vec3f(x * 8,  y * 8,  t)
            + 0.25   * noisex vec3f(x * 16, y * 16, t * 2 + 4) // offset! important
            + 0.125  * noisex vec3f(x * 32, y * 32, t * 4 + 8)
            + 0.0625 * noisex vec3f(x * 64, y * 64, t * 8 + 12)
            + 0.03125* noisex vec3f(x *128, y *128, t * 16 + 16)
            ;*/
      auto res = noisex vec3f (x * 8, y * 8, t);
      res = clamp(0, 1, res);
      
      // auto n = 0.5f * noise2(x * 4 + t, y * 4)+0.25;
      // n = clamp(0, 1, n);
      // auto n2 = vec3f(n, n * n, n * 2);
      auto n2 = vec3f (res);
      return n2;
      // return transition(&f2, &n2, smoothstep(0.3, 0.5, dist + noise2(x * 2 + 100, y * 2) * 0.1f));
    }
    fun1(0, 0);
    sdlfun(&fun4);
    U u;
    u.F = 15;
    printf("comparison 0x%08x\n", float:15);
    writeln("u.i is $$void*:u.I");
    auto tuple = (2, 3);
    writeln("Tuple is $$tuple[0], $$tuple[1]. ");
    int pow2(int i) {
      int res = 1;
      while (i--) res = res * 2;
      return res;
    }
    (int, int) frob;
    frob[0] = 15;
    writeln "frob is $frob";
    alias size = 4;
    auto test = [for bin <-
      [for tuple <- cross ([for i <- 0..2: i] x size): int[size]:tuple]:
      sum [for tup <- zip (bin, [for z <- 0..size:
      pow2(size-z-1)]): tup[0] * tup[1]]].eval;
    writeln("test is $$string-of type-of test: $test");
    return 0;
    onExit writeln("Exit 4. ");
  }
}
