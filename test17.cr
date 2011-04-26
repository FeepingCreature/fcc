module test17;

import sdl, std.random, std.math;
extern(C) int time(int*);

void main() {
  screen (800, 800);
  int offs;
  set-handler (Error) invoke-exit "return";
  define-exit "return" return;
  while true {
    cls vec3f(0);
    offs ++;
    auto rng = getPRNG 23;
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
