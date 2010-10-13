module teapot;
import sys, sdl, opengl;

c_include "math.h";
c_include "time.h";

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
    auto idcount = atoi toStringz lines[0];
    while auto id <- lines[1 .. idcount + 1] {
      int[16] temp;
      temp[] = [for st <- splitAt(",", iter_one id): atoi toStringz st].eval[];
      res.indices ~= temp;
    }
    lines = lines[idcount + 1 .. lines.length];
  }
  {
    auto vertcount = atoi toStringz lines[0];
    while auto vert <- lines[1 .. vertcount + 1] {
      auto split = splitAt(",", iter_one vert).eval;
      vec3f temp;
      while int i <- 0..3
        temp[i] = std.string.atof(split[i]);
      res.vecs ~= temp;
    }
  }
  writeln "Read from $fn: $(res.indices.length) index sets, $(res.vecs.length) vertices. ";
  return res;
}

int fps, last_time;
float t;
void drawScene(DataSet ds) {
  glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  glTranslatef (0, 0, -6);
  // glRotatef (t, 1, 0.1, 0);
  // glRotatef (180, 1, 0, 0);
  glRotatef (t, 0, 1, 0);
  t -= 1;
  int i;
  while auto ind <- ds.indices {
    float f = (i++) * 1.0 / ds.indices.length;
    glColor3f (f, f, f);
    vec3f vcross(vec3f a, vec3f b) {
      return vec3f(a[1]*b[2] - b[1]*a[2], a[2]*b[0] - b[2]*a[0], a[0]*b[1] - b[0]*a[1]);
    }
    float vdot(vec3f a, vec3f b) {
      return a[0]*b[0] + a[1]*b[1] + a[2]*b[2];
    }
    float vlength(vec3f a) {
      return sqrtf(vdot(a, a));
    }
    vec3f vnormal(vec3f a) {
      return a / vlength(a);
    }
    vec3f blend(vec3f from, vec3f to, float u) {
      return from + (to - from) * u;
    }
    void bezier2(float u, vec3f[] field, vec3f* dest) {
      vec3f[5] temp = void;
      temp[0] = blend(field[0], field[1], u);
      temp[1] = blend(field[1], field[2], u);
      temp[2] = blend(field[2], field[3], u);
      temp[3] = blend(temp[0], temp[1], u);
      temp[4] = blend(temp[1], temp[2], u);
      *dest = blend(temp[3], temp[4], u);
    }
    vec3f[16] input = void;
    while auto k <- 0..16 {
      input[k] = ds.vecs[ind[k] - 1];
    }
    void bezier3(float u, float v, vec3f* dest) {
      vec3f[4] temp = void;
      bezier2(u, input[0..4], &temp[0]);
      bezier2(u, input[4..8], &temp[1]);
      bezier2(u, input[8..12], &temp[2]);
      bezier2(u, input[12..16], &temp[3]);
      bezier2(v, temp[], dest);
    }
    using Quads {
      int x, y;
      alias subdiv = 8;
      auto factor = 1.0 / subdiv;
      while (x, y) <- cross (0..subdiv, 0..subdiv) {
        float u = x * 1.0 / subdiv, v = y * 1.0 / subdiv;
        int x2, y2;
        vec3f[4] quad = void;
        int k;
        while (x2, y2) <- [for id <- [0, 1, 3, 2]: (cross (0..2, 0..2))[id]] {
          float u2 = u + factor * x2, v2 = v + factor * y2;
          bezier3(u2, v2, &quad[k++]);
        }
        auto normal = vcross(quad[1]-quad[0], quad[3]-quad[0]);
        auto angle = vdot(vnormal(normal), vnormal(vec3f(0.6, 0.3, -1)));
        if (angle < 0) angle = 0;
        glColor3f vec3f(angle);
        [for v <- quad: glVertex3f v].eval;
      }
    }
  }
  SDL_GL_SwapBuffers();
  fps ++;
  auto ct = time(cast(time_t*) 0);
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
  auto ds = parse("newell_teaset/teapot");
  SDL_Init (SDL_INIT_VIDEO);
  auto flags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_RESIZABLE;
  SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
  auto surf = SDL_SetVideoMode (640, 480, 0, flags);
  if !surf quit(1);
  initGL;
  resizeWindow (640, 480);
  while true {
    drawScene(ds);
    if update(surf) quit(0);
  }
}
