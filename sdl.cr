module sdl;

public import csdl;
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

void pset(int x, int y, vec3f col) {
  auto p = &((int*:surf.pixels)[y * int:surf.pitch / 4 + x]);
  vec3i ii = vec3i(0xff0000, 0xff00, 0xff);
  vec3f ff = vec3f(ii);
  vec3i i = void;
  fastfloor3f (col * ff, &i);
  *p = (i & ii).sum;
}

bool[1024] keyPressed, keyPushed;

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
