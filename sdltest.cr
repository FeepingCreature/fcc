module test;

import sdl, std.c.time;
import simplex;

void sdlfun(vec3f delegate(float, float, float) dg) {
  SDL_Init(32); // video
  auto args = SDL_ANYFORMAT | SDL_RESIZABLE;
  auto surface = SDL_Surface*: SDL_SetVideoMode(640, 480, 0, args);
  void resize(int w, int h) {
    SDL_FreeSurface surface;
    surface = SDL_Surface*: SDL_SetVideoMode (w, h, 0, args);
  }
  vec2i mousePos;
  bool _clicked;
  bool _mouseDown;
  bool clicked() { return _clicked; }
  bool mouseDown() { return _mouseDown; }
  bool update() {
    _clicked = false;
    bool doResize;
    (int, int) resizeTo;
    while SDL_PollEvent &SDL_Event ev using ev {
      if type == SDL_QUIT return true;
      if type == SDL_VIDEORESIZE {
        (doResize, resizeTo)
          = (true, resize.(w, h));
      }
      if type == SDL_MOUSEMOTION {
        mousePos = vec2i(motion.(x, y));
      }
      if type == SDL_MOUSEBUTTONDOWN {
        _clicked = true;
        _mouseDown = true;
        mousePos = vec2i(button.(x, y));
      }
      if type == SDL_MOUSEBUTTONUP {
        _mouseDown = false;
        mousePos = vec2i(button.(x, y));
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
  }
  void flip() { SDL_Flip surface; }
  void pset(int x, int y, int color) {
    auto p = &((int*:surface.pixels)[y * int:surface.w]);
    p[x] = color;
  }
  void line(int fromx, fromy, tox, toy, int color) {
    auto pos = vec2i (fromx, fromy), to = vec2i (tox, toy);
    // Thank you Wikipedia.
    auto d = vec2i ((to - pos).(abs(x), abs(y)));
    auto s = vec2i(1, 1);
    if (pos.x >= to.x) s.x = -1;
    if (pos.y >= to.y) s.y = -1;
    int error = d.(x - y);
    pset(pos, color);
    auto p = &((int*:surface.pixels)[pos.y * int:surface.w]);
    while pos.x != to.x || pos.y != to.y {
      // onSuccess pset(pos, color);
      onSuccess p[pos.x] = color;
      auto e2 = 2 * error;
      if (e2 > -d.y) {
        error -= d.y;
        pos.x += s.x;
      }
      if (e2 < d.x) {
        error += d.x;
        pos.y += s.y;
        p += s.y * int:surface.w;
      }
    }
  }
  void box(int fromx, fromy, tox, toy, int color) {
    if (fromx > tox) (fromx, tox) = (tox, fromx);
    if (fromy > toy) (fromy, toy) = (toy, fromy);
    auto from = vec2i (fromx, fromy), to = vec2i (tox, toy);
    for (int y <- from.y .. to.y + 1) {
      auto p = &((int*:surface.pixels)[y * int:surface.w]);
      for (int x <- from.x .. to.x + 1) {
        p[x] = color;
      }
    }
  }
  auto bits = new int[32*32];
  auto last = time null;
  int drawMode;
  int step;
  while true {
    // run();
    // draw grid
    for 0..10
      box surface.(rand()%w, rand()%h, rand()%w, rand()%h, rand());
    for (int y <- 0..32+1) {
      for (int x <- 0..32+1) {
        line(vec2i(10, 10) + vec2i(0, y * 10), vec2i(32*10+10, 10) + vec2i(0, y * 10), -1);
        line(vec2i(10, 10) + vec2i(x * 10, 0), vec2i(10, 32*10+10) + vec2i(x * 10, 0), -1);
      }
    }
    for (int y <- 0..32) {
      for (int x <- 0..32) {
        auto pos = vec2i(10, 10) + vec2i(x * 10, y * 10), to = pos + vec2i(9, 9);
        if (mouseDown() && mousePos.(x >= pos.x && x <= to.x && y >= pos.y && y <= to.y)) {
          if (clicked()) drawMode = 1-bits[y*32+x];
          writeln "clicked @$mousePos";
          bits[y*32+x] = drawMode;
        }
        int col;
        if (bits[y*32+x]) col = -1;
        box(pos + vec2i(1, 1), to, col);
      }
    }
    // line(vec2i(10, 10), vec2i(50, 80), -1);
    flip;
    fps ++;
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
