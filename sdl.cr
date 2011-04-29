module sdl;

public import c.SDL.SDL;
import std.string;

SDL_Surface* surf;

void blit(SDL_Surface* from, (vec2i, vec2i) srcrect,
          SDL_Surface* to, (vec2i, vec2i) dstrect) {
  SDL_Rect sdlrect1, sdlrect2;
  for (int i, SDL_Rect* rp) <- zip(0..2, [&sdlrect1, &sdlrect2])
    using *rp {
      auto rect = [srcrect, dstrect][i];
      x = short:rect[0].x;
      y = short:rect[0].y;
      w = short:(rect[1].x - rect[0].x);
      h = short:(rect[1].y - rect[0].y);
    }
  auto res = SDL_UpperBlit(from, &sdlrect1, to, &sdlrect2);
  if res raise-error new Error "SDL_UpperBlit: $res: $(CToString SDL_GetError())";
}

void blit(SDL_Surface* from, vec2i to) {
  blit(from, (vec2i(0, 0), vec2i(from.(w, h))),
       surf, (to, to + vec2i(from.(w, h))));
}

void screen(int w, h, bool fullscreen = false, bool hidden = false) {
  SDL_Init(32); // video
  int cfg = SDL_SWSURFACE;
  if fullscreen cfg |= SDL_FULLSCREEN;
  
  if hidden
    surf = SDL_CreateRGBSurface(cfg, w, h, 32, 0xff0000, 0xff00, 0xff, 0);
  else
    surf = SDL_SetVideoMode(w, h, 32, cfg);
  if !surf raise-error new Error "Couldn't init screen with $w x $h - $(CToString SDL_GetError())! ";
}

class SDLQuit : Error {
  void init() { super.init "SDL_QUIT"; }
}

void pset(int x, int y, int col) {
  if (x >= surf.w || x < 0 || y >= surf.h || y < 0) return;
  (int*:surf.pixels)[y * int:surf.pitch / 4 + x] = col;
}

int floatToIntColor(vec3f col) {
  vec3i ii = vec3i(0xff0000, 0xff00, 0xff);
  vec3f ff = vec3f(ii);
  vec3i i = void;
  fastfloor3f (col * ff, &i);
  return (i & ii).sum;
}

void pset(int x, int y, vec3f col) {
  if (x >= surf.w || x < 0 || y >= surf.h || y < 0) return;
  auto p = &((int*:surf.pixels)[y * int:surf.pitch / 4 + x]);
  *p = floatToIntColor(col);
}

// Blatantly ripped off from WP:Bresenham

void line(int from-x, from-y, to-x, to-y, vec3f col = vec3f(1)) {
  auto from = vec2i(from-x, from-y), to = vec2i(to-x, to-y);
  auto icol = floatToIntColor col;
  bool steep = eval abs(to.y - from.y) > abs(to.x - from.x);
  if steep
    (from.(x, y), to.(x, y)) = (from.(y, x), to.(y, x));
  if from.x > to.x
    (from, to) = (to, from);
  auto
    delta-x = to.x - from.x,
    delta-y = abs(to.y - from.y),
    error = delta-x / 2;
  int ystep = [-1, 1][eval from.y < to.y], y = from.y;
  for (int x = from.x; x <= to.x; ++x) {
    if steep pset(y, x, icol); else pset(x, y, icol);
    error -= delta-y;
    if error < 0 {
      y += ystep;
      error += delta-x;
    }
  }
}

void hline(int from-x, y, to-x, int icol) {
  auto surf = surf;
  if (y >= surf.h || y < 0) return;
  from-x = [from-x, 0][eval from-x < 0];
  if (to-x >= surf.w) to-x = surf.w - 1;
  auto p = &((int*:surf.pixels)[y * int:surf.pitch / 4 + from-x]);
  auto delta = to-x - from-x + 1;
  delta = [delta, 0][eval delta < 0];
  while delta >= 4 {
    *(int, int, int, int)*:p = (icol x 4);
    delta -= 4;
    p += 4;
  }
  while (delta --) {
    *(p++) = icol;
  }
}

void cls(vec3f col) {
  int icol = floatToIntColor col;
  for (int y = 0; y < surf.h; ++y) {
    hline(0, y, surf.w, icol);
  }
}

// This one is WP:Midpoint circle algorithm. <3 you WP.
void circle(int x0, y0, radius, vec3f col = vec3f(1), vec3f fill = vec3f(-1)) {
  int f = 1 - radius, ddF_x = 1, ddF_y = - 2 * radius, x, y = radius;
  
  auto icol = floatToIntColor col;
  
  bool fillIt = eval fill.x >= 0;
  
  int fcol;
  if fillIt {
    fcol = floatToIntColor fill;
    hline(x0 - radius + 1, y0, x0 + radius - 1, fcol);
  }
  
  int lastY;
  while x < y {
    // ddF_x == 2 * x + 1;
    // ddF_y == -2 * y;
    // f == x*x + y*y - radius*radius + 2*x - y + 1;
    if f >= 0 {
      --y; ddF_y += 2; f += ddF_y;
    }
    ++x; ddF_x += 2; f += ddF_x;
    if (fillIt && lastY != y) {
      lastY = y;
      hline(x0 - x + 1, y0 - y, x0 + x - 1, fcol);
      hline(x0 - x + 1, y0 + y, x0 + x - 1, fcol);
    }
    if (x < y) {
      hline(x0 - y + 1, y0 - x, x0 + y - 1, fcol);
      hline(x0 - y + 1, y0 + x, x0 + y - 1, fcol);
    }
    for auto tup <- cross([x, -x], [y, -y]) {
      pset(x0 + tup[0], y0 + tup[1], icol);
      pset(x0 + tup[1], y0 + tup[0], icol);
    }
  }
  // fill in the corners
  pset(x0, y0 + radius, icol);
  pset(x0, y0 - radius, icol);
  pset(x0 + radius, y0, icol);
  pset(x0 - radius, y0, icol);  
}

bool x 1024 keyPressed, keyPushed;

void flip() {
  SDL_Flip surf;
  for int i <- 0..keyPushed.length
    keyPushed[i] = false;
  while SDL_PollEvent &SDL_Event ev using ev {
    if type == 12
      raise-error new SDLQuit;
    else if type == SDL_KEYDOWN using key.keysym {
      if (sym < keyPressed.length) { keyPressed[sym] = true; keyPushed[sym] = true; }
    }
    else if type == SDL_KEYUP using key.keysym {
      if (sym < keyPressed.length) { keyPressed[sym] = false; }
    }
  }
}

void saveBMP(string s) {
  auto p = toStringz s;
  onSuccess mem.free p;
  auto res = SDL_SaveBMP_RW (surf, SDL_RWFromFile (p, "wb"), 1);
  if res == -1 {
    writeln "error - $(CToString SDL_GetError())";
    _interrupt 3;
  }
}
