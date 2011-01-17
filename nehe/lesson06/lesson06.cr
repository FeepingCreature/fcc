module lesson06;

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

import std.c.stdio, std.c.stdlib, opengl, sdl;

alias SCREEN_SIZE = (640, 480);
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
  glMatrixMode GL_PROJECTION;
  glLoadIdentity;
  gluPerspective (45.0, ratio, 0.1, 100);
  glMatrixMode GL_MODELVIEW;
  glLoadIdentity;
}

void handleKeyPress(SDL_keysym* keysym )
{
  if (keysym.sym == SDLK_ESCAPE) quit 0;
  if (keysym.sym == SDLK_F1) SDL_WM_ToggleFullScreen surface;
}

context rot {
  float x, y, z;
}

GLuint[1] texture;

void loadGLTextures() {
  auto status = false;
  auto TextureImage = ["data/nehe.bmp".SDL_RWFromFile("rb").SDL_LoadBMP_RW(1)];
  if TextureImage[0] {
    status = true;
    glGenTextures (1, &texture[0]);
    using GL_TEXTURE_2D {
      glBindTexture texture[0];
      using *TextureImage[0]
        glTexImage2D (0, 3, w, h, 0, GL_BGR, GL_UNSIGNED_BYTE, pixels);
      
      GL_TEXTURE_MIN_FILTER.glTexParameteri GL_LINEAR;
      GL_TEXTURE_MAG_FILTER.glTexParameteri GL_LINEAR;
    }
    if TextureImage[0]
      SDL_FreeSurface TextureImage[0];
  }
}

void initGL() {
  glShadeModel GL_SMOOTH;
  loadGLTextures;
  glEnable GL_TEXTURE_2D;
  glClearColor(0, 0, 0, 0.5);
  glClearDepth(1);
  glEnable GL_DEPTH_TEST;
  glDepthFunc GL_LEQUAL;
  glHint (GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
}

context timing {
  int t0, frames;
}

alias X = (1, 0, 0);
alias Y = (0, 1, 0);
alias Z = (0, 0, 1);

void drawGLScene() {
  glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  glTranslatef (0, 0, -5);
  using rot {
    glRotatef (x, X);
    glRotatef (y, Y);
    glRotatef (z, Z);
  }
  
  GL_TEXTURE_2D.glBindTexture texture[0];
  
  auto corners = cross [1, -1] x 3;
  /*
   1  1  1 |0
   1  1 -1 |1
   1 -1  1 |2
   1 -1 -1 |3
  -1  1  1 |4
  -1  1 -1 |5
  -1 -1  1 |6
  -1 -1 -1 |7
  */
  glBegin GL_QUADS;
  while type-of((0, 0), 0) tup <- [
                  // front face
                  ((0, 1), 6), ((1, 1), 2), ((1, 0), 0), ((0, 0), 4),
                  // back face
                  ((0, 0), 7), ((0, 1), 5), ((1, 1), 1), ((1, 0), 3),
                  // top face
                  ((1, 1), 5), ((1, 0), 4), ((0, 0), 0), ((0, 1), 1),
                  // bottom face
                  ((0, 1), 7), ((1, 1), 3), ((1, 0), 2), ((0, 0), 6),
                  // right face
                  ((0, 0), 3), ((0, 1), 1), ((1, 1), 0), ((1, 0), 2),
                  // left face
                  ((1, 0), 7), ((0, 0), 6), ((0, 1), 4), ((1, 1), 5)]
    {
      glTexCoord2f tup[0];
      glVertex3f corners[tup[1]];
    }
    using rot {
      x = x + 0.01 * 10;
      y = y + 0.006 * 10;
      z = z + 0.013 * 10;
    }
  glEnd;
  
  SDL_GL_SwapBuffers();
  timing.frames++;
  auto t = SDL_GetTicks();
  if (t - timing.t0 >= 5000) using timing {
    auto seconds = (t - t0) / 1000.0;
    auto fps = frames / seconds;
    writeln "$frames frames in $seconds seconds = $fps fps. ";
    t0 = t;
    frames = 0;
  }
}

char[] toString(char* p) {
  return p[0..strlen(p)];
}

int main(string[] args) {
  SDL_Init(SDL_INIT_VIDEO);
  auto videoFlags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_HWPALETTE | SDL_RESIZABLE | SDL_HWSURFACE | SDL_HWACCEL;
  SDL_GL_SetAttribute (SDL_GL_DOUBLEBUFFER, 1);
  surface = SDL_SetVideoMode (SCREEN_SIZE, SCREEN_BPP, videoFlags);
  if (!surface) {
    writeln("Video mode set failed: $(toString(SDL_GetError()))");
    quit 1;
  }
  initGL;
  resizeWindow SCREEN_SIZE;
  bool done;
  while !done {
    SDL_Event ev;
    while SDL_PollEvent(&ev) {
      if (ev.type == SDL_VIDEORESIZE) {
        surface = SDL_SetVideoMode (ev.resize.(w, h), 16, videoFlags);
        resizeWindow ev.resize.(w, h);
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
  quit 0;
  return 0;
}
