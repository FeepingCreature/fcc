module sdl;

public import csdl;
import std.string;

SDL_Surface* surf;

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

void flip() {
  SDL_Flip surf;
  while SDL_PollEvent &SDL_Event ev {
    if ev.type == 12
      raise-error new SDLQuit;
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
