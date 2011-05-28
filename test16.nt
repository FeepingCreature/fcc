module test16;

import sdl, sdl_ttf;
import std.math, std.file, std.random, std.boehm;

void main() {
  initBoehm();
  auto rng = getPRNG 23;
  screen (640, 480);
  auto fc = new TTF_FontClass (void[]: import("Vera.ttf")[], 15);
  auto hw = fc.render "Hello World";
  while true {
    hw.blit display.at vec2i(rng.rand() % display.w, rng.rand() % display.h);
    flip;
  }
}
