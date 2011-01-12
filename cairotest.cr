module cairotest;

import sdl;

extern(C) float sinf(float);
extern(C) float cosf(float);
alias PI = 3.1415926538;
extern(C) int time(int*);

c_include "cairo/cairo.h";
c_include "GL/gl.h";
c_include "GL/glu.h";
c_include "GL/glx.h";
extern(C) cairo_device_t* cairo_glx_device_create (Display* dpy, GLXContext gl_ctx);
extern(C) cairo_surface_t* cairo_gl_surface_create_for_window (cairo_device_t *device, Window win, int width, height);
extern(C) void cairo_gl_surface_swapbuffers (cairo_surface_t*);

defmode cairo-context x "prefix cairo_ first-arg x";
defmode cairo-pattern p "prefix pattern_ first-arg p";
defmode sdl-window w "prefix SDL_ first-arg w";

void resizeWindow(int width, height) {
  if !height height = 1;
  auto ratio = width * 1.0 / height;
  glViewport(0, 0, width, height);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  // gluPerspective(45.0, ratio, 0.1, 100);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();
}

void initGL() {
  glShadeModel(GL_SMOOTH);
  glClearColor(0, 0, 0, 0);
  glClearDepth(1);
}

void main() {
  writeln "Open SDL Window .. ";
  SDL_Init (SDL_INIT_VIDEO);
  SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
  auto attribs = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_HWPALETTE | SDL_RESIZABLE | SDL_HWSURFACE | SDL_HWACCEL;
  auto window = SDL_SetVideoMode (640, 480, 32, attribs);
  writeln "got $window";
  initGL;
  resizeWindow(640, 480);
  auto backup =
    (glXGetCurrentDisplay, glXGetCurrentDrawable, glXGetCurrentContext);
  auto dev = cairo_glx_device_create (backup[0], backup[2]);
  glXMakeCurrent backup;
  
  writeln "create surf for $dev";
  writeln "post: $(glXGetCurrentContext), $(glXGetCurrentDisplay)";
  auto surface = cairo_gl_surface_create_for_window
    (dev, backup[1], window.w, window.h);
  
  float f = 0;
  void draw() {
    f += 0.1;
    glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    glLoadIdentity();
    mode cairo-context cairo_create surface {
      onSuccess destroy; // social commentary lol
      set_source_rgb (0, 0.1, 0.1);
      paint;
      auto p  = vec2f(25.6 , 128.0),
           p1 = vec2f(102.4, 230.4),
           p2 = vec2f(153.6, 25.6 ),
           p3 = vec2f(230.4, 128.0);
      
      move_to p;
      curve_to (p1, p2, p3);
      set_source_rgb (1.0, 1.0, 1.0);
      set_line_width 10;
      stroke;
      
      set_source_rgba (1, 0.2, 0.2, 0.6);
      set_line_width 6;
      move_to p;   line_to p1;
      move_to p2;  line_to p3;
      stroke;
      
      set_source_rgb (1, 1, 0.8);
      set_line_width 1;
      auto center = vec2f(320, 240);
      int i;
      while float it <- [for x <- 0 .. 180*4: x / 4.0] {
        auto delta = vec2f(sinf(it * PI / 180) * 200, cosf(it * PI / 180) * 200);
        delta *= (0.5 + 0.5 * sinf (f * it * PI / 180 + f));
        move_to (center - delta);
        line_to (center + delta);
        // if ((++i) % 5 == 0) stroke;
      }
      stroke;
    }
    cairo_gl_surface_swapbuffers surface;
  }
  
  int fps, lastTime = time null;
  bool update() mode sdl-window window {
    draw();
    fps ++;
    Flip;
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
