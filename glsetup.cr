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
  glEnable GL_DEPTH_TEST;
  glEnable GL_COLOR_MATERIAL;
  glDepthFunc GL_LESS; // lequal is bad for mesa
  glEnable GL_TEXTURE_2D;
  glHint (GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
  return true;
}

SDL_Surface* delegate(int, int) regenSurf;

vec2i mousepos;

bool mouseClicked, mousePressed;

bool[1024] keyPressed, keyPushed;

bool update(SDL_Surface* surface) {
  for int i <- 0..keyPushed.length
    keyPushed[i] = false;
  mouseClicked = false;
  
  SDL_GL_SwapBuffers();
  SDL_Event ev = void;
  
  while SDL_PollEvent(&ev) using ev {
    if type == SDL_QUIT return true;
    else if type == SDL_VIDEORESIZE using resize {
      regenSurf (w, h);
      resizeWindow (w, h);
    }
    else if type == SDL_MOUSEMOTION using motion {
      mousepos = vec2i(x, y);
    }
    else if type == SDL_MOUSEBUTTONDOWN using button {
      mouseClicked = true;
      mousePressed = true;
    }
    else if type == SDL_MOUSEBUTTONUP using button {
      mousePressed = false;
    }
    else if type == SDL_KEYDOWN using key.keysym {
      if (sym < keyPressed.length) { keyPressed[sym] = true; keyPushed[sym] = true; }
    }
    else if type == SDL_KEYUP using key.keysym {
      if (sym < keyPressed.length) { keyPressed[sym] = false; }
    }
    else writeln "type $(ev.type)";
  }
  return false;
}

void swap() { SDL_GL_SwapBuffers(); }

void delegate()[] gl-context-callbacks;

SDL_Surface* setup-gl() {
  SDL_Init (SDL_INIT_VIDEO);
  auto flags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_RESIZABLE;
  // SDL_GL_SetAttribute(SDL_GL_ACCELERATED_VISUAL, 1);
  regenSurf = new delegate SDL_Surface*(int w, int h) {
    writeln "regenSurf($w, $h, 0, $flags)";
    auto res = SDL_SetVideoMode (w, h, 0, flags);
    if !res quit(1);
    initGL;
    // IMPORTANT: init gl FIRST
    resizeWindow (w, h);
    for (auto dg <- gl-context-callbacks)
      dg();
    return res;
  };
  return regenSurf(640, 480);
}
