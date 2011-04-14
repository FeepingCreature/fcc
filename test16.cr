module test16;

import sdl, sdl_ttf;
import std.math, std.file, std.random;

(float, float) e_to_i_times(float x) { return (cos(x), sin(x)); }

void main() {
  auto rng = getPRNG 23;
  screen (640, 480);
  auto fc = new TTF_FontClass (void[]: import("Vera.ttf"), 15);
  auto hw = fc.render "Hello World";
  while true {
    blit(hw, vec2i(rng.rand() % surf.w, rng.rand() % surf.h));
    flip;
  }
}
