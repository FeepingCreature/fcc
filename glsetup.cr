module glsetup;

import opengl, sdl;

void quit(int code) {
  SDL_Quit();
  exit(code);
}

int resizeWindow(int w, int h) {
  if !h
    h = 1;
  auto ratio = w * 1.0 / h;
  glViewport(0, 0, w, h);
  glMatrixMode GL_PROJECTION;
  glLoadIdentity;
  gluPerspective(45.0, ratio, 0.1, 100.0);
  glMatrixMode GL_MODELVIEW;
  glLoadIdentity;
  return true;
}

int initGL() {
  glShadeModel GL_SMOOTH;
  glClearColor (0 x 4);
  glClearDepth 1;
  glEnable GL_DEPTH_TEST;
  glDepthFunc GL_LESS; // lequal is bad for mesa
  glEnable GL_TEXTURE_2D;
  glHint (GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
  return true;
}

void delegate(int, int) regenSurf;

(int, int) mousepos;

bool update(SDL_Surface* surface) {
  SDL_Event ev = void;
  while SDL_PollEvent(&ev) using ev {
    if type == SDL_QUIT return true;
    if type == SDL_VIDEORESIZE using resize {
      regenSurf (w, h);
      resizeWindow (w, h);
      return false;
    }
    if type == SDL_MOUSEMOTION using motion {
      mousepos = (x, y);
    }
    // writeln "type $(ev.type)";
  }
  return false;
}

void swap() { SDL_GL_SwapBuffers(); }

SDL_Surface* setup-gl() {
  // this has issues; why?!
  // SDL_Init (SDL_INIT_VIDEO);
  SDL_InitSubSystem (SDL_INIT_VIDEO);
  auto flags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_RESIZABLE;
  SDL_GL_SetAttribute(SDL_GL_ACCELERATED_VISUAL, 1);
  SDL_Surface* surf;
  regenSurf = delegate void(int w, int h) {
    surf = SDL_SetVideoMode (w, h, 0, flags);
  };
  regenSurf(640, 480);
  if !surf quit(1);
  initGL;
  // IMPORTANT: init gl FIRST
  resizeWindow (surf.w, surf.h);
  return surf;
}
