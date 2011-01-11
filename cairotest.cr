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
  auto surface = cairo_image_surface_create_for_data window.(pixels, CAIRO_FORMAT_ARGB32, w, h, pitch);
  
  float f = 0;
  void draw() {
    f += 0.1;
    auto cr = cairo_create (surface);
    mode cairo-context cr {
      onSuccess destroy; // social commentary lol
      set_source_rgb (0, 0, 0);
      paint;
      auto rect = (10, 10, 250, 100 + 50 * sinf (f * 0.1));
      set_line_width 5;
      set_source_rgb (0, 255, 0);
      rectangle rect;
      stroke;
      set_source_rgb (0, 0, 255);
      rectangle rect;
      fill;
      text_extents_t te;
      set_source_rgb (255, 255, 255);
      select_font_face ("Georgia",
          CAIRO_FONT_SLANT_NORMAL, CAIRO_FONT_WEIGHT_BOLD);
      set_font_size 36;
      text_extents ("Hello World", &te);
      move_to (130 - te.(width / 2 + x_bearing), 40 - te.(height / 2 + y_bearing));
      show_text "Hello World";
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
