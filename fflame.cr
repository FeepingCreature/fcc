module fflame;

import sdl, std.random.mersenne, std.math, std.thread, std.time, std.string;

template vex3f(alias A) <<EOF
  alias vex3f = A[0]~".(vec3f("~A[1].replace("%", "x")~", "~A[1].replace("%", "y")~", "~A[1].replace("%", "z")~"))";
EOF

void main(string[] args) {
  int w = 1440, h = 900; bool fs = false;
  if (args.length > 2 && args[2] == "full") { (w, h, fs) = (1920, 1080, true); }
  screen (w, h, fullscreen => fs);
  set-handler (SDLQuit) invoke-exit "return";
  define-exit "return" return;
  
  vec2f delegate(vec2f)[] funlist;
  
  funlist ~= delegate vec2f(vec2f f) { return f; };
  funlist ~= delegate vec2f(vec2f f) { return vec2f(sin f.x, sin f.y); };
  funlist ~= delegate vec2f(vec2f f) { return f / f.lensq; };
  funlist ~= delegate vec2f(vec2f f) using f { auto r2 = lensq, s = sin r2, c = cos r2; return vec2f(x * s - y * c, x * c + y * s); };
  funlist ~= delegate vec2f(vec2f f) using f { return vec2f((x - y) * (x + y), 2 * x * y) / sqrtf lensq; };
  
  int seed;
  if args.length > 1 seed = args[1].atoi();
  auto mt = new MersenneTwister(seed);
  
  float randf() { return (mt.rand() & 0x7fff_ffff) * 1f / 0x7fff_ffff; }
  vec3f rand3f() { return vec3f(randf() x 3); }
  vec4f rand4f() { return vec4f(randf() x 4); }
  
  vec2f delegate(vec2f) transform(vec2f delegate(vec2f) dg) {
    float[12] factors;
    for int i <- 0..12 {
      factors[i] = randf() * 4 - 2;
      //factors[i] = factors[i].pow 2;
    }
    return new delegate vec2f(vec2f v) {
      auto fp = &factors; alias f = *fp;
      vec2f v2 = void;
      v2.x = v.x * f[0] + v.y * f[1] + f[2];
      v2.y = v.x * f[3] + v.y * f[4] + f[5];
      v2 = dg(v2);
      v.x = v2.x * f[6] + v2.y * f[7] + f[8];
      v.y = v2.x * f[9] + v2.y * f[10] + f[11];
      return v;
    };
  }
  
  (vec4f, vec2f delegate(vec2f))[] funs;
  for 0..mt.rand()%2 + 3
    funs ~= (rand4f(), transform funlist[mt.rand()%$]);
  
  auto field = new vec4f[w * h];
  for int i <- 0..field.length field[i] = vec4f(0);

  long iters;
  auto tp = new ThreadPool(4);
  void runSteps(int count, MersenneTwister mt) {
    auto pos = vec2f(0), col = vec4f(0);
    iters += count;
    auto scale = vec2i(w, h) / 4;
    for 0..count {
      auto index = mt.rand() % funs.length;
      alias fun = funs[index];
      col = (col + fun[0]) * 0.5;
      pos = fun[1] pos;
      auto ipos = vec2i(int:((pos.x + 2) * scale.x), int:((pos.y + 2) * scale.y));
      if ipos.(((eval x >= 0) & (eval y >= 0)) & ((eval x < w) & (eval y < h))) {
        auto fp = &field[ipos.y * w + ipos.x];
        alias f = *fp;
        f.x += col.x;
        f.y += col.y;
        f.z += col.z;
        f.w += 1 / col.w;
      }
    }
  }
  bool shutdown;
  void worker(MersenneTwister mt) while !shutdown runSteps(1024, mt);
  void startWorker(MersenneTwister mt) { auto worker = &worker; tp.addTask new delegate void() worker mt;; }
  onExit {
    shutdown = true;
    tp.waitComplete;
    writeln "shut down. ";
  }
  for 0..4 startWorker new MersenneTwister mt;
  auto start = sec();
  while true {
    float basefactor = float:(double:iters / (w * h));
    writeln "base factor $basefactor; $(basefactor/(sec() - start)) / s";
    for (int y, int x) <- cross(0..h, 0..w) {
      auto f = field[y * w + x];
      if f[1] > 0.01 {
        auto c = f;
        float count = f[1] / basefactor;
        c = c  * log(count + 1) / c.w;
        c *= 0.707;
        c = mixin vex3f!("c", "min(%, 1)");
        alias gamma = 2.2;
        c = mixin vex3f!("c", "%.pow (1 / gamma)");
        pset (x, y, c.xyz);
      }
    }
    flip;
  }
}
