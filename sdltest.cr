module test;

import sdl, std.c.time;

void sdlfun(vec3f delegate(float, float, float) dg) {
  SDL_Init(32); // video
  auto args = SDL_ANYFORMAT | SDL_RESIZABLE;
  auto surface = SDL_Surface*: SDL_SetVideoMode(640, 480, 0, args);
  void resize(int w, int h) {
    SDL_FreeSurface surface;
    surface = SDL_Surface*: SDL_SetVideoMode (w, h, 0, args);
  }
  bool update() {
    bool doResize;
    (int, int) resizeTo;
    while SDL_PollEvent &SDL_Event ev using ev {
      if type == SDL_QUIT return true;
      if type == SDL_VIDEORESIZE {
        (doResize, resizeTo)
          = (true, resize.(w, h));
      }
    }
    // only run once
    if doResize
      resize resizeTo;
    return false;
  }
  auto start = time null;
  float t = 0;
  int fps;
  void run() {
    for (int y = 0; y < surface.h; ++y) {
      auto p = &((int*:surface.pixels)[y * int:surface.w]);
      for (int x = 0; x < surface.w; ++x) {
        int red = x, green = y, blue = x + y;
        *(p++) = ((red & 0xff) << 16) + ((green & 0xff) << 8) + (blue & 0xff);
      }
    }
    SDL_Flip(surface);
    fps ++;
  }
  auto last = time null;
  while true {
    run();
    if (update()) return;
    if (auto tvar = time null) > last {
      last = tvar;
      writeln("FPS: $fps");
      fps = 0;
    }
  }
}

int main(string[] args) {
  sdlfun(null);
}
