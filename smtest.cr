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
  t -= 1;
  void drawCube() {
    auto points = cross ([-1, 1] x 3);
    using Quads {
      while int idx <- [
        0, 1, 3, 2,  4, 5, 7, 6, // top, bottom
        0, 1, 5, 4,  1, 3, 7, 5,  3, 2, 6, 7,  2, 0, 4, 6] { // sides
        glColor3f ((idx / 7.0) x 3);
        glVertex3f points[idx];
      }
    }
  }
  
  glTranslatef (0, 2 * sin(t / 64), 0);
  drawCube();
  SDL_GL_SwapBuffers();
  fps ++;
  auto ct = time(time_t*:null);
  if ct != last_time {
    last_time = ct;
    writeln "FPS: $fps";
    fps = 0;
  }
}

int update(SDL_Surface* surface) {
  SDL_Flip surface;
  SDL_Event ev = void;
  while SDL_PollEvent(&ev) {
    if ev.type == 12 return 1; // QUIT
  }
  return 0;
}

int main(int argc, char** argv) {
  t = 0;
  
  SDL_Init (SDL_INIT_VIDEO);
  auto flags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_RESIZABLE;
  SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
  auto surf = SDL_SetVideoMode (640, 480, 0, flags);
  if !surf quit(1);
  initGL;
  // IMPORTANT: init gl FIRST
  resizeWindow (640, 480);
  while true {
    drawScene();
    if update(surf) quit(0);
  }
}
