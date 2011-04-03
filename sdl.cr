module sdl;

c_include "SDL/SDL.h";

SDL_Surface* surf;

void screen(int w, h) {
  SDL_Init(32); // video
  surf = SDL_SetVideoMode(w, h, 32, SDL_ANYFORMAT);
}

class SDLQuit : Error {
  void init() { super.init "SDL_QUIT"; }
}

void pset(int x, int y, vec3f col) {
  auto p = &((int*:surf.pixels)[y * int:surf.w + x]);
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
