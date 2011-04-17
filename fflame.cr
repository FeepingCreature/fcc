module fflame;

import sdl, std.random, std.math, std.thread, std.time, std.string;

alias atoi = std.string.atoi;
alias atof = std.string.atof;

extern(C) int feenableexcept(int);
extern(C) int feclearexcept(int);
alias FE_INVALID = 0x1;
alias FE_DENORM = 0x2;
alias FE_DIVBYZERO = 0x4;
alias FE_OVERFLOW = 0x8;
alias FE_UNDERFLOW = 0x10;
alias FE_INEXACT = 0x20;

template vex3f(alias A) <<EOF
  alias vex3f = A[0]~".(vec3f("~A[1].replace("%", "x")~", "~A[1].replace("%", "y")~", "~A[1].replace("%", "z")~"))";
EOF

class FPUEx : Error {
  void init() { super.init "FPU Exception"; }
}

FPUEx _fpuex;
void init() { _fpuex = new FPUEx; }

extern(C) void function(int) signal(int, void function(int) fn);
alias SIGFPE = 8;
void sigfun(int i) {
  raise-error _fpuex;
}

void main(string[] args) {
	(string exec, args) = args[(0, 1..$)];
  int w = 640, h = 480; bool fs = false;
  if (args.length > 1 && args[1] == "full") { (w, h, fs, args) = (1920, 1080, true, args[0..1]~args[1..$]); }
  set-handler (SDLQuit) invoke-exit "return";
  define-exit "return" return;
  
  auto fpmask = (FE_DIVBYZERO | FE_INVALID | FE_OVERFLOW);
  fpucw = short:(fpucw & ¬fpmask);
  signal(SIGFPE, &sigfun);
  
  void delegate(vec2f*)[] funlist;
  
  funlist ~= delegate void(vec2f* fp) { };
  funlist ~= delegate void(vec2f* fp) { auto f = *fp; *fp = vec2f(sin f.x, sin f.y); };
  funlist ~= delegate void(vec2f* fp) { auto f = *fp; *fp = f / f.lensq; };
  funlist ~= delegate void(vec2f* fp) { auto f = *fp; using f:: auto r2 = lensq, s = sin r2, c = cos r2; *fp = vec2f(x * s - y * c, x * c + y * s); };
  // (x - y) * (x + y) = x*x + x*y - y*x - y*y
  // funlist ~= delegate vec2f(vec2f f) using f { return vec2f((x - y) * (x + y), 2 * x * y) / sqrt lensq; };
  funlist ~= delegate void(vec2f* fp) { auto f = *fp; auto fprod = f * f; float lsq = fprod.(x+y); *fp = vec2f(fprod.(x-y), 2*f.x*f.y) / std.math.sqrtf lsq; };
  
  int seed;
  if args.length (seed, args) = (args[0].atoi(), args[1..$]);
  auto rng = getPRNG seed;
  
  IRandom rng2;
  float mul = 1;
  int iterlimit;
  string targetfile;
  
  if args.length {
    (int num, args) = (args[0].atoi(), args[1..$]);
    if num
      rng2 = getPRNG num;
  }
  float xatof(string s) {
    if s.find(":") == -1 return s.atof();
    (string a, string b) = s.slice(":");
    return a.atoi() * 1f / b.atoi();
  }
  if args.length (mul, args) = (xatof(args[0]), args[1..$]);
  if args.length (iterlimit, args) = (args[0].atoi(), args[1..$]);
  if args.length (targetfile, args) = args[(0, 1..$)];
  
  bool hidden = eval targetfile;
  
  screen (w, h, fullscreen => fs, hidden => hidden);
  
  float randf(IRandom r) { return (r.rand() & 0x7fff_ffff) * 1f / 0x7fff_ffff; }
  vec3f rand3f() { return vec3f(randf(rng) x 3); }
  vec4f rand4f() { return vec4f(randf(rng) x 4); }
  
  vec2f delegate(vec2f) transform(void delegate(vec2f*) dg) {
    float[12] factors;
    for int i <- 0..12 {
      factors[i] = randf(rng) * 4 - 2;
      factors[i] = factors[i].pow 3;
    }
    for int i <- [2, 5, 8, 11] factors[i] /= 5;
    if rng2 {
      for int i <- 0..12
        factors[i] += (randf(rng2) - 0.5) * 2 * mul;
    }
    auto meep = funlist;
    return new delegate vec2f(vec2f v) {
      auto fp = &factors; alias f = *fp;
      vec2f v2 = void;
      v2.x = v.x * f[0] + v.y * f[1] + f[2];
      v2.y = v.x * f[3] + v.y * f[4] + f[5];
      dg(&v2);
      v.x = v2.x * f[6] + v2.y * f[7] + f[8];
      v.y = v2.x * f[9] + v2.y * f[10] + f[11];
      return v;
    };
  }
  
  (vec4f, vec2f delegate(vec2f))[] funs;
  for 0..rng.rand()%2 + 3
    funs ~= (rand4f(), transform funlist[rng.rand()%$]);
  
  auto field = new vec4f[w * h];
  for int i <- 0..field.length field[i] = vec4f(0);

  long iters; int nanfails; long misses;
  auto tp = new ThreadPool(4);
  void runSteps(int count, IRandom rng) {
    set-handler (FPUEx fe) invoke-exit "reset-pos";
    float randf() { return (rng.rand() & 0x7fff_ffff) * 1f / 0x7fff_ffff; }
    auto pos = vec2f(0), col = vec4f(0);
    iters += count;
    int w = w, h = h; // local copies
    auto scale = vec2f(w, h) / 4f;
    int start;
    define-exit "reset-pos" {
      pos = vec2f(randf() x 2); col = vec4f(0);
      feclearexcept fpmask;
      nanfails ++;
    }
    int graceperiod = 20; // give color time to stabilize
    // done this way so reset-pos can resume correctly
    for start <- start..count {
      // hopelessly out of bounds
      if (pos.lensq > 1000000000000.0) { pos = vec2f(randf() x 2); col = vec4f(0); graceperiod = 20; }
      auto index = rng.rand() % funs.length;
      alias fun = funs[index];
      col = (col + fun[0]) * vec4f(0.5);
      pos = fun[1] pos;
      if graceperiod graceperiod--;
      else {
        auto ipos = vec2i(int:((pos.x + 2) * scale.x), int:((pos.y + 2) * scale.y));
        if ipos.(((eval x >= 0) & (eval y >= 0)) & ((eval x < w) & (eval y < h))) {
          auto fp = &field[ipos.y * w + ipos.x];
          alias f = *fp;
          f.x += col.x;
          f.y += col.y;
          f.z += col.z;
          f.w += 1 / col.w;
        } else misses++;
      }
    }
  }
  bool shutdown;
  void worker(IRandom rng) while !shutdown runSteps(1024, rng);
  void startWorker(IRandom rng) { auto worker = &worker; tp.addTask new delegate void() worker rng;; }
  onExit {
    shutdown = true;
    if !iterlimit tp.waitComplete;
    writeln "shut down. ";
  }
  if iterlimit {
    writeln "start 4 $(iterlimit / 4)-workers";
    for 0..4{
      auto dg = &runSteps;
      auto subrng = getPRNG rng;
      auto count = iterlimit / 4;
      tp.addTask new delegate void() dg (count, subrng);;
    }
  } else {
    for 0..4 startWorker getPRNG rng;
  }
  auto start = sec();
  while true {
    if iterlimit { writeln "wait for threadpool completion"; tp.waitComplete; writeln "done"; }
    float basefactor = float:(double:iters / (w * h));
    writeln "base factor $basefactor; $(basefactor/(sec() - start)) / s - $iters, $nanfails nans, $(double:misses * 100.0 / double:iters)% misses";
    if basefactor > 0.01 {
      for (int y, int x) <- cross(0..h, 0..w) {
        auto f = field[y * w + x];
        if f[1] > 0.01 {
          auto c = f;
          float count = f[1] / basefactor;
          c = c * log(count + 1) / c.w;
          c *= 0.707;
          c = mixin vex3f!("c", "min(%, 1)");
          alias gamma = 2.2;
          c = mixin vex3f!("c", "%.pow (1 / gamma)");
          pset (x, y, c.xyz);
        }
      }
    }
    if targetfile
      targetfile.saveBMP;
    flip;
    if iterlimit return;
  }
}
