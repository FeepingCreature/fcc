module sdl;

public import c.SDL.SDL;
import std.string;

class Surface {
  SDL_Surface* back;
  RefCounted rc;
  void free() { SDL_FreeSurface back; }
  alias release = rc.release();
  alias claim = rc.claim();
  alias w = back.w;
  alias h = back.h;
  void flip() SDL_Flip back;
  void init() {
    claim;
    rc.onZero = &free;
  }
  void init(SDL_Surface* surf) {
    back = surf;
    init();
  }
}

int floatToIntColor(vec3f col) {
  vec3i ii = vec3i(0xff0000, 0xff00, 0xff);
  vec3f ff = vec3f(ii);
  vec3i i = void;
  fastfloor3f (col * ff, &i);
  return (i & ii).sum;
}

class SDL-Error : Error {
  void init(string fun, int res) {
    super.init "$fun: $res: $(CToString SDL_GetError())";
  }
}

class SDLQuit : Error {
  void init() { super.init "SDL_QUIT"; }
}

class Area {
  Surface surf;
  (vec2i, vec2i) rect;
  alias x0 = rect[0].x;
  alias y0 = rect[0].y;
  alias x1 = rect[1].x;
  alias y1 = rect[1].y;
  alias w = x1 - x0, h = y1 - y0;
  void free() { surf.free; }
  void init(Surface s) {
    surf = s;
    rect[0] = vec2i(0, 0);
    rect[1] = vec2i(surf.w, surf.h);
  }
  Area at(int x, int y) {
    auto res = new Area surf;
    res.rect = rect;
    res.rect[0] += vec2i(x, y);
    return res;
  }
  void blit(Area dest) {
    SDL_Rect sdlrect1, sdlrect2;
    for (int i, SDL_Rect* rp) <- zip(0..2, [&sdlrect1, &sdlrect2])
      using *rp {
        auto r = [rect, dest.rect][i];
        (x, y) = r[0].(short:x, short:y);
        (w, h) = (short:(r[1].x - r[0].x), short: (r[1].y - r[0].y));
      }
    auto res = SDL_UpperBlit (surf.back, &sdlrect1, dest.surf.back, &sdlrect2);
    if res raise-error new SDL-Error("SDL_UpperBlit", res);
  }
  void pset(int x, y, vec3f col) {
    if !( x0 <= x < x1  &&  y0 <= y < y1 ) return;
    x += x0; y += y0;
    if !( 0 <= x < surf.w  &&  0 <= y < surf.h ) return;
    
    auto p = &((int*:surf.back.pixels)[y * int:surf.back.pitch / 4 + x]);
    *p = floatToIntColor col;
  }
  void pset(int x, y, int icol) {
    if !( x0 <= x < x1  &&  y0 <= y < y1 ) return;
    x += x0; y += y0;
    if !( 0 <= x < surf.w  &&  0 <= y < surf.h ) return;
    
    auto p = &((int*:surf.back.pixels)[y * int:surf.back.pitch / 4 + x]);
    *p = icol;
  }
  void hline(int from-x, y, to-x, vec3f col) {
    if !(y0 <= y < y1) return;
    y += y0;
    if !(0 <= y < surf.h) return;
    from-x += x0; to-x += x0;
    
    if (to-x < from-x) (from-x, to-x) = (to-x, from-x);
    
    from-x = [from-x, 0]       [eval from-x < 0];
    to-x   = [to-x, surf.w - 1][eval to-x >= surf.w];
    if (from-x >= surf.w || to-x < 0) return;
    
    auto icol = floatToIntColor col;
    auto p = &((int*:surf.back.pixels)[y * int:surf.back.pitch / 4 + from-x]);
    auto delta = to-x - from-x + 1;
    while delta >= 4 {
      *(int, int, int, int)*:p = (icol x 4);
      delta -= 4;
      p += 4;
    }
    while (delta --) {
      *(p++) = icol;
    }
  }
  void vline(int x, from-y, to-y, vec3f col) {
    if !(x0 <= x < x1) return;
    x += x0;
    if !(0 <= x < surf.w) return;
    from-y += y0; to-y += y0;
    
    if (to-y < from-y) (from-y, to-y) = (to-y, from-y);
    
    from-y = [from-y, 0]       [eval from-y < 0];
    to-y   = [to-y, surf.h - 1][eval to-y >= surf.h];
    if (from-y >= surf.h || to-y < 0) return;
    
    auto icol = floatToIntColor col;
    auto pitch = int:surf.back.pitch / 4;
    auto p = &((int*:surf.back.pixels)[from-y * pitch + x]);
    auto delta = to-y - from-y + 1;
    while (delta --) {
      *p = icol;
      p += pitch;
    }
  }
  void cls(vec3f col) {
    for int y <- 0..h-1
      hline(0, y, w-1, col);
  }
  // Blatantly ripped off from WP:Bresenham
  void line(int from-x, from-y, to-x, to-y, vec3f col = vec3f(1)) {
    // no need to do bounds checking here; pset is already safe
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
  // This one is WP:Midpoint circle algorithm. <3 you WP.
  void circle(int x0, y0, radius,
    xspread = 0, yspread = 0,
    vec3f col = vec3f(1), vec3f fill = vec3f(-1)) {
    int f = 1 - radius, ddF_x = 1, ddF_y = - 2 * radius, x, y = radius;
    
    bool fillIt = eval fill.x >= 0;
    
    if fillIt {
      hline(x0 - radius + 1, y0, x0 + radius - 1 + xspread, fill);
    }
    
    auto icol = floatToIntColor col;
    
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
        hline(x0 - x + 1, y0 - y          , x0 + x - 1 + xspread, fill);
        hline(x0 - x + 1, y0 + y + yspread, x0 + x - 1 + xspread, fill);
      }
      if (x < y) {
        hline(x0 - y + 1, y0 - x          , x0 + y - 1 + xspread, fill);
        hline(x0 - y + 1, y0 + x + yspread, x0 + y - 1 + xspread, fill);
      }
      for auto tup <- zip(cross([1, 0], [1, 0]), cross([1, -1], [1, -1])) {
        pset(x0 + tup[1][0] * x + tup[0][0] * xspread,
            y0 + tup[1][1] * y + tup[0][1] * yspread, icol);
        pset(x0 + tup[1][0] * y + tup[0][0] * xspread,
            y0 + tup[1][1] * x + tup[0][1] * yspread, icol);
      }
    }
    // fill in the sides/corners
    hline(x0, y0 + radius + yspread, x0 + xspread, col);
    hline(x0, y0 - radius          , x0 + xspread, col);
    vline(x0 + radius + xspread, y0, y0 + yspread, col);
    vline(x0 - radius          , y0, y0 + yspread, col);
    // fill in the middle
    if fillIt {
      for (int i = y0; i <= y0 + yspread; ++i) {
        hline(x0 - radius + 1, i, x0 + radius - 1 + xspread, fill);
      }
    }
  }
  void rounded_box(int x0, y0, x1, y1,
    radius = 5, vec3f col = vec3f(1), vec3f fill = vec3f(-1))
  {
    // translate into circle call
    auto cx = x0 + radius, xspread = x1 - cx;
    xspread = [xspread, 0][eval xspread < 0];
    auto cy = y0 + radius, yspread = y1 - cy;
    yspread = [yspread, 0][eval yspread < 0];
    circle(cx, cy, radius, xspread => xspread, yspread => yspread,
          col => col, fill => fill);
  }
}

Area display;

void screen(int w, h, bool fullscreen = false, bool hidden = false) {
  SDL_Init(32); // video
  int cfg = SDL_SWSURFACE;
  if fullscreen cfg |= SDL_FULLSCREEN;
  
  SDL_Surface* surf;
  if hidden
    surf = SDL_CreateRGBSurface(cfg, w, h, 32, 0xff0000, 0xff00, 0xff, 0);
  else
    surf = SDL_SetVideoMode(w, h, 32, cfg);
  if !surf raise-error new Error "Couldn't init screen with $w x $h - $(CToString SDL_GetError())! ";
  
  display = new Area new Surface surf;
}

bool x 1024 keyPressed, keyPushed;

void flip() {
  display.surf.flip();
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
  auto res = SDL_SaveBMP_RW (display.surf.back, SDL_RWFromFile (p, "wb"), 1);
  if res == -1 {
    writeln "error - $(CToString SDL_GetError())";
    _interrupt 3;
  }
}
