module teapot;
import sys, sdl, opengl;

void quit(int code) {
  SDL_Quit();
  exit(code);
}

int resizeWindow(int w, int h) {
  if !h
    h = 1;
  auto ratio = w * 1.0 / h;
  glViewport(0, 0, w, h);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  gluPerspective(45.0, ratio, 0.1, 100.0);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();
  return true;
}

int initGL() {
  glShadeModel(GL_SMOOTH);
  glClearColor(0, 0, 0, 0);
  glClearDepth(1);
  glEnable(GL_DEPTH_TEST);
  glDepthFunc(GL_LEQUAL);
  glHint(GL_PERSPECTIVE_CORRECTION_HINT, GL_NICEST);
  return true;
}

context Triangles {
  alias onUsing = glBegin(GL_TRIANGLES);
  alias onExit = glEnd();
}

context Quads {
  alias onUsing = glBegin(GL_QUADS);
  alias onExit = glEnd();
}

template iter_one(T) <<EOF
  class one {
    T t;
    bool done;
    T step() {
      done = true;
      return t;
    }
    bool ivalid() {
      return eval !done;
    }
  }
  one iter_one(T t) {
    auto res = new one;
    res.t = t;
    return res;
  }
EOF

class DataSet {
  int[16][auto~] indices;
  vec3f[auto~] vecs;
}

import std.file, std.string;
DataSet parse(string fn) {
  auto res = new DataSet;
  auto lines = splitAt("\n", readfile open fn).eval[];
  {
    auto idcount = atoi(toStringz(lines[0]));
    while auto id <- lines[1 .. idcount + 1] {
      int[16] temp;
      temp[] = [for st <- splitAt(",", iter_one id): atoi(toStringz(st))].eval[];
      res.indices ~= temp;
    }
    lines = lines[idcount + 1 .. lines.length];
  }
  {
    auto vertcount = atoi(toStringz(lines[0]));
    while auto vert <- lines[1 .. vertcount + 1] {
      auto split = splitAt(",", iter_one vert).eval;
      vec3f temp;
      while int i <- 0..3
        temp[i] = std.string.atof(split[i]);
      res.vecs ~= temp;
    }
  }
  writeln("Read from $fn: $(res.indices.length) index sets, $(res.vecs.length) vertices. ");
  return res;
}

float t;
void drawScene(DataSet ds) {
  glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity();
  glTranslatef(0, 0, -6);
  glRotatef(t, 0.1, 1, 0);
  t += 0.01;
  int i;
  while auto ind <- ds.indices {
    float f = (i++) * 1.0 / ds.indices.length;
    glColor3f(f, f, f);
    using Quads {
      // lol
      while auto id <- [for i <- cross ([0, 1, 2, 4, 5, 6, 8, 9, 10], 0..4): [for i <- 0..16: [i, i+1, i+5, i+4]][i[0]][i[1]]] {
        glVertex3f ds.vecs[ind[id] - 1];
      }
    }
  }
  SDL_GL_SwapBuffers();
}

int update(SDL_Surface* surface) {
  SDL_Flip(surface);
  SDL_Event ev;
  while SDL_PollEvent(&ev) {
    if ev.type == 12 return 1; // QUIT
  }
  return 0;
}

int main(int argc, char** argv) {
  t = 0;
  auto ds = parse("newell_teaset/teapot");
  SDL_Init(SDL_INIT_VIDEO);
  auto flags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_HWPALETTE | SDL_RESIZABLE | SDL_HWSURFACE | SDL_HWACCEL;
  SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
  auto surf = SDL_SetVideoMode(640, 480, 0, SDL_OPENGL);
  if !surf quit(1);
  initGL();
  resizeWindow(640, 480);
  while true {
    drawScene(ds);
    if update(surf) quit(0);
  }
}
