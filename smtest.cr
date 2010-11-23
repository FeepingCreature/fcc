module smtest;
import sys, sdl, opengl, std.c.math, std.c.time;

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
  glDepthFunc GL_LEQUAL;
  glHint (GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
  return true;
}

int fps, last_time;

float t = 0;

void drawScene() {
  glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  glTranslatef (0, 0, -6);
  // glRotatef (t, 1, 0.1, 0);
  // glRotatef (180, 1, 0, 0);
  glRotatef (t, 0, 1, 0);
  t -= 0.01;
  void drawCube() {
    auto points = cross ((0..2) x 3);
    using Quads {
      while int idx <- [
        0, 1, 3, 2,  4, 5, 7, 6, // top, bottom
        0, 1, 5, 4,  1, 3, 7, 5,  3, 2, 6, 7,  2, 0, 4, 6] { // sides
        glColor3f ((idx / 7.0) x 3);
        glVertex3f points[idx];
      }
    }
  }
  
  glScalef (0.2 x 3);
  glTranslatef (0, 2 * sin(t / 64), 0);
  while auto vec <- cross (-5 .. 5) x 3 {
    glTranslatef vec;
    drawCube();
    glTranslatef -vec3f(vec);
  }
  SDL_GL_SwapBuffers();
  fps ++;
  auto ct = time(time_t*:null);
  if ct != last_time {
    last_time = ct;
    writeln "FPS: $fps";
    fps = 0;
  }
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

int main(int argc, char** argv) {
  // this has issues; why?!
  SDL_Init (SDL_INIT_VIDEO);
  auto flags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_RESIZABLE;
  SDL_GL_SetAttribute(SDL_GL_ACCELERATED_VISUAL, 1);
  SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
  SDL_Surface* surf;
  regenSurf = delegate void(int w, int h) {
    surf = SDL_SetVideoMode (w, h, 0, flags);
  };
  regenSurf(640, 480);
  if !surf quit(1);
  initGL;
  // IMPORTANT: init gl FIRST
  resizeWindow (640, 480);
  while true {
    drawScene();
    if update(surf) quit(0);
  }
}
