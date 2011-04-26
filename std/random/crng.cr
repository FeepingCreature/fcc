module std.random.crng;

import std.random.base, std.c.stdlib;

// no rand_r on windows, fo shame. 
platform(default) <<EOF

  class CRNG : IRandom {
    int seed;
    void init(int s) { seed = s; }
    int rand() { return rand_r &seed; }
  }
  
  void init() {
    engines ~= (
      delegate IRandom(int s) { return new CRNG s; },
      delegate IRandom(IRandom ir) { return new CRNG ir.rand(); },
      1); // low-qual C RNG
  }
EOF
