module cairotest;

import sdl;

extern(C) float sinf(float);
extern(C) int time(int*);

c_include "cairo/cairo.h";

defmode cairo-context x "prefix cairo_ first-arg x";
defmode sdl-window w "prefix SDL_ first-arg w";

void main() {
  writeln "Open SDL Window .. ";
  SDL_Init (SDL_INIT_VIDEO);
  auto window = SDL_SetVideoMode (640, 480, 32, SDL_HWSURFACE | SDL_RESIZABLE);
  SDL_LockSurface window;
  cairo_surface_t* surface;
  using *window
    surface = cairo_image_surface_create_for_data (pixels, CAIRO_FORMAT_ARGB32, w, h, pitch);
  
  float f = 0;
  void draw() {
    f += 0.1;
    auto cr = cairo_create (surface);
    mode cairo-context cr {
      set_source_rgb (0, 0, 0);
      rectangle (0, 0, image_surface_get_width surface, image_surface_get_height surface);
      fill;
      onSuccess destroy; // social commentary lol
      auto rect = (10, 10, 100, 100 + 50 * sinf (f * 0.1));
      set_line_width 5;
      set_source_rgb (0, 255, 0);
      rectangle rect;
      stroke;
      set_source_rgb (0, 0, 255);
      rectangle rect;
      fill;
    }
  }
  
  int fps, lastTime = time null;
  bool update() mode sdl-window window {
    draw();
    fps ++;
    cairo_surface_flush surface;
    UnlockSurface;
    Flip;
    LockSurface;
    while PollEvent &Event ev {
      if ev.type == 12 return true;
    }
    if (time null != lastTime) {
      writeln "$fps fps";
      fps = 0; lastTime = time null;
    }
    return false;
  }
  while true if update() return;
}
