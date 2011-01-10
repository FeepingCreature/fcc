module cairotest;

import sdl;

c_include "cairo/cairo.h";

defmode cairo x "prefix cairo_ first-arg x";

void main() {
  writeln "Open SDL Window .. ";
  SDL_Init (SDL_INIT_VIDEO);
  auto window = SDL_SetVideoMode (640, 480, 32, SDL_SWSURFACE);
  SDL_LockSurface window;
  cairo_surface_t* surface;
  using *window
    surface = cairo_image_surface_create_for_data (pixels, CAIRO_FORMAT_ARGB32, w, h, pitch);
  auto cr = cairo_create (surface);
  SDL_FillRect(window, null, 0xffffffff);
  
  mode cairo cr {
    set_line_width 5;
    set_source_rgb (0, 255, 0);
    rectangle (10, 10, 100, 100);
    stroke;
    set_source_rgb (0, 0, 255);
    rectangle (10, 10, 100, 100);
    fill; destroy;
  }
  
  bool update() {
    cairo_surface_flush surface;
    SDL_UnlockSurface window;
    SDL_Flip window;
    SDL_LockSurface window;
    SDL_Event ev;
    while SDL_PollEvent &ev {
      if ev.type == 12 return true;
    }
    return false;
  }
  while true if update() return;
}
