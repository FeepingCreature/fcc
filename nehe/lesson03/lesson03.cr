module lesson03;

import sys;

/*
 * This code was created by Jeff Molofee '99 
 * (ported to Linux/SDL by Ti Leggett '01)
 * (ported to fcc by feep '10)
 *
 * If you've found this code useful, please let me know.
 *
 * Visit Jeff at http://nehe.gamedev.net/
 * 
 * or for port-specific comments, questions, bugreports etc. 
 * email to leggett@eecs.tulane.edu
 */

c_include "stdio.h";
c_include "stdlib.h";
c_include "GL/gl.h";
c_include "GL/glu.h";
c_include "SDL/SDL.h";

alias SCREEN_WIDTH = 640;
alias SCREEN_HEIGHT = 480;
alias SCREEN_BPP = 16;

SDL_Surface* surface;

void quit(int code) {
  SDL_Quit();
  exit(code);
}

void resizeWindow(int width, height) {
  if !height height = 1;
  auto ratio = width * 1.0 / height;
  glViewport(0, 0, width, height);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  gluPerspective(45.0, ratio, 0.1, 100);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();
}

void handleKeyPress(SDL_keysym* keysym )
{
  if (keysym.sym == SDLK_ESCAPE) quit(0);
  if (keysym.sym == SDLK_F1) SDL_WM_ToggleFullScreen(surface);
}

void initGL() {
  glShadeModel(GL_SMOOTH);
  glClearColor(0, 0, 0, 0);
  glClearDepth(1);
  glEnable(GL_DEPTH_TEST);
  glDepthFunc(GL_LEQUAL);
  glHint(GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
}

context timing {
  int t0, frames;
}

void drawGLScene() {
  glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity();
  
  glTranslatef(-1.5, 0, -6.0);
  glBegin(GL_TRIANGLES);
    while auto tup <- [((1, 0, 0), ( 0,  1, 0)),
                       ((0, 1, 0), (-1, -1, 0)),
                       ((0, 0, 1), ( 1, -1, 0))] {
      glColor3f(tup[0]);
      glVertex3f(tup[1]);
    }
  glEnd();
  
  glTranslatef(3, 0, 0);
  glColor3f(0.5, 0.5, 1.0);
  glBegin(GL_QUADS);
    [for tup <- zip ([-1, 1, 1, -1], [1, 1, -1, -1]): glVertex3f(tup, 0)].eval;
  glEnd();
  
  SDL_GL_SwapBuffers();
  timing.frames++;
  auto t = SDL_GetTicks();
  if (t - timing.t0 >= 5000) using timing {
    auto seconds = (t - t0) / 1000.0;
    auto fps = frames / seconds;
    writeln("$frames frames in $seconds seconds = $fps fps. ");
    t0 = t;
    frames = 0;
  }
}

char[] toString(char* p) {
  return p[0..strlen(p)];
}

int main(int argc, char** argv) {
  SDL_Init(SDL_INIT_VIDEO);
  auto videoFlags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_HWPALETTE | SDL_RESIZABLE | SDL_HWSURFACE | SDL_HWACCEL;
  SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
  surface = SDL_SetVideoMode(SCREEN_WIDTH, SCREEN_HEIGHT, SCREEN_BPP, videoFlags);
  if (!surface) {
    writeln("Video mode set failed: $(toString(SDL_GetError()))");
    quit(1);
  }
  initGL();
  resizeWindow(SCREEN_WIDTH, SCREEN_HEIGHT);
  bool done;
  while !done {
    SDL_Event ev;
    while SDL_PollEvent(&ev) {
      if (ev.type == SDL_VIDEORESIZE) {
        surface = SDL_SetVideoMode(ev.resize.w, ev.resize.h, 16, videoFlags);
        resizeWindow(ev.resize.w, ev.resize.h);
      }
      if (ev.type == SDL_KEYDOWN) {
        handleKeyPress(&ev.key.keysym);
      }
      if (ev.type == SDL_QUIT) {
        done = true;
      }
    }
    drawGLScene();
  }
  quit(0);
  return 0;
}
