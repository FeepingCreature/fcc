module lesson09;
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

alias SCREEN_WIDTH = 640, SCREEN_HEIGHT = 480, SCREEN_BPP = 16;
alias NumStars = 256;
bool twinkle;

struct Star {
  int r, g, b;
  float dist, angle;
}

Star[NumStars] stars;

float zoom = -15, tilt = 90;

SDL_Surface* surface;

GLuint[1] texture;

void quit(int code) {
  SDL_Quit;
  exit code;
}

void loadGLtextures() {
  auto TextureImage = [SDL_LoadBMP_RW(SDL_RWFromFile("data/star.bmp", "rb"), 1)];
  glGenTextures (1, texture.ptr);
  glBindTexture (GL_TEXTURE_2D, texture[0]);
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  using *TextureImage[0]
    glTexImage2D (GL_TEXTURE_2D, 0, 3, w, h, 0, GL_BGR, GL_UNSIGNED_BYTE, pixels);
  if TextureImage[0]
    SDL_FreeSurface (TextureImage[0]);
}

void resizeWindow(int width, height) {
  if !height height = 1;
  auto ratio = width * 1.0 / height;
  glViewport(0, 0, width, height);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity;
  gluPerspective(45.0, ratio, 0.1, 100);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity;
}

void handleKeyPress(SDL_keysym* keysym) using *keysym
{
  if (sym == SDLK_ESCAPE) quit 0;
  if (sym == SDLK_F1) SDL_WM_ToggleFullScreen(surface);
  if (sym == SDLK_t) twinkle = 1-twinkle;
  if (sym == SDLK_UP) tilt -= 0.5;
  if (sym == SDLK_DOWN) tilt += 0.5;
  if (sym == SDLK_PAGEUP) zoom -= 0.2;
  if (sym == SDLK_PAGEDOWN) zoom += 0.2;
}

void initGL() {
  glShadeModel GL_SMOOTH;
  glClearColor vec4f(0);
  glClearDepth(1);
  loadGLtextures;
  glEnable GL_TEXTURE_2D;
  glBlendFunc (GL_SRC_ALPHA, GL_ONE);
  glEnable GL_BLEND;
  while int i <- 0..NumStars using stars[i] {
    angle = 0;
    dist = i * 5.0 / NumStars;
    (r, g, b) = (rand() % 256) x 3;
  }
  glDepthFunc GL_LEQUAL;
  glHint(GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
}

int t0, frames;

alias X = (1, 0, 0), Y = (0, 1, 0), Z = (0, 0, 1);

void drawGLScene() {
  glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  
  glBindTexture (GL_TEXTURE_2D, texture[0]);
  float spin = 0;
  while int i <- 0..NumStars using stars[i] {
    glLoadIdentity;
    glTranslatef (0, 0, zoom);
    glRotatef (tilt, X);
    glRotatef (angle, Y);
    glTranslatef (dist, 0, 0);
    glRotatef (-angle, Y);
    glRotatef (-tilt, X);
    if (twinkle) {
      using stars[NumStars - i - 1] glColor4f(r / 255.0, g / 255.0, b / 255.0, 255);
      glBegin GL_QUADS;
        while auto tup <- [((0, 0), (-1, -1)), ((1, 0), (1, -1)), ((1, 1), (1, 1)), ((0, 1), (-1, 1))] {
          glTexCoord2f (tup[0]);
          glVertex3f (tup[1], 0);
        }
      glEnd;
    }
    glRotatef (spin, Z);
    glColor4f(r / 255.0, g / 255.0, b / 255.0, 255);
    glBegin GL_QUADS;
      while auto tup <- [((0, 0), (-1, -1)), ((1, 0), (1, -1)), ((1, 1), (1, 1)), ((0, 1), (-1, 1))] {
        glTexCoord2f (tup[0]);
        glVertex3f (tup[1], 0);
      }
    glEnd;
    spin += 0.2;
    angle += i * 0.5 / NumStars;
    dist -= 0.05;
    if dist < 0 {
      dist += 5;
      (r, g, b) = (rand() % 256) x 3;
    }
  }
  
  SDL_GL_SwapBuffers;
  frames++;
  auto t = SDL_GetTicks;
  if (t - t0 >= 5000) {
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
  initGL;
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
    drawGLScene;
  }
  quit 0;
  return 0;
}
