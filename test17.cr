module test17;

import sdl, std.random, std.math;
extern(C) int time(int*);

// Thank You WP
int jenkins_hash(string key) {
  int hash;
  for int ch <- key {
    hash += ch;
    hash += hash << 10;
    hash xor= hash >> 6;
  }
  hash += hash << 3;
  hash xor= hash >> 11;
  hash += hash << 15;
  return hash;
}

template AssocArray(T) <<EOT
  alias Key = T[0];
  alias Value = T[1];
  struct AssocArray {
    (Key, Value)[] store;
    Value nullval;
    bool hasNull;
    int length;
    Value* getp(Key k) {
      Key nil;
      if k == nil return [null, &nullval][hasNull];
      if !store.length return null;
      auto pos = (jenkins_hash k) % store.length;
      while bool looping = true {
        if store[pos][0] == k
          return &store[pos][1];
        if store[pos][0] == nil
          looping = false;
        else pos ++;
      }
      return null;
    }
  }
EOT

void main() {
  screen (800, 800);
  // AssocArray!(string, Object) aa;
  int offs;
  set-handler (Error) invoke-exit "return";
  define-exit "return" return;
  while true {
    auto rng = getPRNG 23;
    cls vec3f(0);
    offs ++;
    for int j <- 0..64 {
      float jf = j / 64f;
      for int i <- 0..j {
        auto angle = i * PI2 / j, s = sin angle, c = cos angle, c2 = cos (angle * offs * 0.01 + offs * 0.2) * 0.5 + 0.5;
        circle(surf.w / 2 + int:(surf.w * 0.45 * jf * s), surf.h / 2 + int:(surf.h * 0.45 * jf * c), int:(c2 * 16), vec3f(1), fill => vec3f(randf(rng) x 3));
      }
    }
    flip;
  }
}
