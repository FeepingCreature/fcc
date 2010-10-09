module test;
import sys, sdl;

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

c_include "stdlib.h";
c_include "math.h";
c_include "fenv.h";
c_include "unistd.h";
c_include "time.h";

void sdlfun(float[3] delegate(float, float, float) dg) {
  SDL_Init(32); // video
  SDL_Surface* surface = cast(SDL_Surface*) SDL_SetVideoMode(320, 240, 0, SDL_ANYFORMAT);
  int update() {
    SDL_Flip(surface);
    SDL_Event ev;
    while SDL_PollEvent(&ev) {
      if ev.type == 12 return 1; // QUIT
    }
    return 0;
  }
  auto start = time(cast(int*) 0);
  float t = 0;
  int fps;
  void run() {
    fesetround(FE_DOWNWARD);
    t = t + 0.05;
    int factor1 = 255, factor2 = 256 * 255, factor3 = 256 * 256 * 255;
    float f1f = factor1, f2f = factor2, f3f = factor3;
    for (int y = 0; y < surface.h; ++y) {
      auto p = &((cast(int*) surface.pixels)[y * cast(int) surface.w]);
      for (int x = 0; x < surface.w; ++x) {
        auto f = dg(cast(float) x / surface.w, cast(float) y / surface.h, t);
        *(p++) = cast(int) (f1f * f[2]) + cast(int) (f2f * f[1]) & factor2 + cast(int) (f3f * f[0]) & factor3;
      }
    }
    fps ++;
  }
  auto last = time(cast(int*) 0);
  while 1 {
    run();
    if (update()) return;
    if time(cast(int*) 0) > last {
      last = time(cast(int*) 0);
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
    writeln("T::$(t.stringof)");
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

int main(int argc, char** argv) {
  // use Boehm GC
  /* mem.malloc_dg = &GC_malloc;
  void* myCalloc(int a, b) {
    auto len = a * b;
    auto res = sys.mem.malloc(len);
    char ch;
    (cast(char*) res)[0 .. len] = [for 0..len: ch];
    return res;
  }
  void* myRealloc(void* a, size_t b) { return GC_realloc(a, cast(int) b); }
  mem.calloc_dg = &myCalloc;
  mem.realloc_dg = &myRealloc;
  mem.free_dg = &GC_free;*/
  auto cdg = mem.calloc_dg;
  void* myCalloc(int a, b) {
    // printf("Allocate %i, %i\n", a, b);
    if (a*b > 65536) {
      printf("Excessive allocation: %i, %i\n", a, b);
      *cast(int*) 0=0;
    }
    return cdg(a, b);
  }
  mem.calloc_dg = &myCalloc;
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
  writeln "Alloc subclass. ";
  auto sub = new Subclass;
  writeln "Do sup cast";
  auto sup = cast(Class) sub;
  writeln("sup is $$cast(void*) sup");
  sup.foo(-5);
  writeln("sub is $$cast(void*) sub");
  sub.iafun();
  sub.ibfun();
  sub.icfun();
  sub.idfun();
  IA ia = sub;
  writeln "call ia on implicit IA cast from sub; ia is $(cast(void*) ia), sub is $(cast(void*) sub), iafun is $(&ia.iafun), on sub would be $(&sub.iafun). ";
  ia.iafun();
  auto ic = cast(IC) ia;
  ic.icfun();
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
  atexit writeln("global is $globvar, $$&globvar, $$*&globvar");
  atexit writeln("Exit. ");
  atexit writeln("Exit 2. ");
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
    atexit writeln("Exit 3. ");
    // 2d simplex noise; see http://staffwww.itn.liu.se/~stegu/simplexnoise/simplexnoise.pdf
    int[512] perm;
    perm[0 .. 256] = [for 0..256: rand() % 256];
    perm[256 .. 512] = perm[0 .. 256];
    int[3][12] grad3;
    {
      int i;
      char[] str = "pp0np0pn0nn0p0pn0pp0nn0n0pp0np0pn0nn";
      auto chp = str[0], chn = str[3];
      for (int k = 0; k < 12; ++k) {
        for (int l = 0; l < 3; ++l) {
          auto ch = str[i++];
          if (ch == chp) grad3[k][l] = 1;
          else if (ch == chn) grad3[k][l] = -1;
        }
      }
    }
    float dot(int[3] whee, float a, float b) {
      return whee[0] * a + whee[1] * b;
    }
    float sqrt3 = sqrtf(3);
    float f2 = 0.5 * (sqrt3 - 1), g2 = (3 - sqrt3) / 6;
    float noise2(float fx, float fy) {
      fesetround(1024);
      float[3] n = void;
      
      float s = (fx + fy) * f2;
      int i = cast(int) (fx + s), j = cast(int) (fy + s);
      
      float t = (i + j) * g2;
      float[3] x = void, y = void;
      x[0] = fx - (i - t);
      y[0] = fy - (j - t);
      
      int i1, j1;
      if x[0] > y[0] i1 = 1;
      else j1 = 1;
      
      {
        auto temp = 1 - 2 * g2;
        x[1] = x[0] - i1 + g2;
        y[1] = y[0] - j1 + g2;
        x[2] = x[0] - temp;
        y[2] = y[0] - temp;
      }
      int ii = i & 255, jj = j & 255;
      
      int[3] gi = void;
      gi[0] = perm[ii + perm[jj]] % 12;
      gi[1] = perm[ii + i1 + perm[jj + j1]] % 12;
      gi[2] = perm[ii + 1  + perm[jj + 1 ]] % 12;
      
      for (int k = 0; k < 3; ++k) {
        float ft = 0.5 - x[k]*x[k] - y[k]*y[k];
        if ft < 0 n[k] = 0;
        else {
          ft = ft * ft;
          n[k] = ft * ft * dot(grad3[gi[k]], x[k], y[k]);
        }
      }
      return 70 * (n[0] + n[1] + n[2]);
    }
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
    float[3] rgb(float r, float g, float b) {
      float[3] res = void;
      res[0] = r;
      res[1] = g;
      res[2] = b;
      return res;
    }
    float[3] transition(float[3]* a, float[3]* b, float f) {
      float finv = 1 - f;
      return rgb(
        (*a)[0] * finv + (*b)[0] * f,
        (*a)[1] * finv + (*b)[1] * f,
        (*a)[2] * finv + (*b)[2] * f
      );
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
    float[3] fun2(float x, float y) {
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
      return rgb(f, f, f);
    }
    float[3] fun3(float x, float y, float t) {
      // auto f2 = fun2(x, y);
      x = x - 0.5;
      y = y - 0.5;
      // auto dist = sqrtf(x * x + y * y);
      auto n = 0.5 * noise2(x * 4 + t, y * 4) + 0.25 * noise2(x * 8, x * 8 + t) + 0.125 * noise2(y * 16 + t, y * 16 + t) + 0.0625 * noise2(x * 32 + t, y * 32 - t * 2);
      // auto n = 0.5 * noise2(x * 4 + t, y * 4)+0.25;
      n = clamp(0, 1, n);
      float[3] n2 = rgb(n, n * n, n * 2);
      return n2;
      // return transition(&f2, &n2, smoothstep(0.3, 0.5, dist + noise2(x * 2 + 100, y * 2) * 0.1));
    }
    fun1(0, 0);
    sdlfun(&fun3);
    U u;
    u.F = 15;
    printf("comparison 0x%08x\n", cast(float) 15);
    writeln("u.i is $$cast(void*) u.I");
    auto tuple = (2, 3);
    writeln("Tuple is $$tuple[0], $$tuple[1]. ");
    int pow2(int i) {
      int res = 1;
      while (i--) res = res * 2;
      return res;
    }
    alias size = 4;
    auto test = [for bin <- [for tuple <- cross [for i <- 0..2: i]^size: cast(int[size]) tuple]: sum [for tup <- zip (bin, [for z <- 0..size: pow2(size-z-1)]): tup[0] * tup[1]]].eval;
    writeln("test is $$typeof(test).stringof: $test");
    auto frobbly = cross [for i <- 0..2: i]^3;
    // writeln "Initial frobbly == $((cast(byte*) &frobbly)[0..44]). ";
    writeln "Test: $$__istep frobbly";
    // writeln "In-between state: $((cast(byte*) &frobbly)[0..44]). "; // 180
    break;
    __istep frobbly;
    break;
    writeln "And $$__istep frobbly. ";
    // writeln "After this, frobbly is $((cast(byte*) &frobbly)[0..44]). "; // 180
    typeof(__istep frobbly) i;
    while i <- frobbly writeln "i => $i";
    return 0;
    atexit writeln("Exit 4. ");
  }
}
