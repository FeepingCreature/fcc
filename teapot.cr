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

context Triangles {
  alias onUsing = glBegin GL_TRIANGLES;
  alias onExit = glEnd;
}

context Quads {
  alias onUsing = glBegin GL_QUADS;
  alias onExit = glEnd;
}

class DataSet {
  int[16][auto~] indices;
  vec3f[auto~] vecs;
}

import std.file, std.string;
DataSet parse(string fn) {
  auto res = new DataSet;
  auto lines = splitAt("\n", [for chunk <- readfile open fn: (string: chunk)]).eval[];
  {
    auto idcount = atoi toStringz lines[0];
    while auto id <- lines[1 .. idcount + 1] {
      int[16] temp;
      temp[] = [for st <- splitAt(",", iterOnce id): atoi toStringz st].eval[];
      res.indices ~= temp;
    }
    lines = lines[idcount + 1 .. lines.length];
  }
  {
    auto vertcount = atoi toStringz lines[0];
    while auto vert <- lines[1 .. vertcount + 1] {
      auto split = splitAt(",", iterOnce vert).eval[];
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
vec3f[] temp;

GLuint teaObj;
int entries;
bool needUpdate;

void drawScene(DataSet ds) {
  glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  glTranslatef (0, 0, -6);
  // glRotatef (t, 1, 0.1, 0);
  // glRotatef (180, 1, 0, 0);
  glRotatef (t, 0, 1, 0);
  t -= 1;
  int vertices;
  if needUpdate {
    needUpdate = false;
    entries = 0;
    vec3f[auto~] data;
    onExit { data.free; }
    while auto ind <- zip (0..-1, ds.indices) {
      float f = ind[0] * 1.0 / ds.indices.length;
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
        input[k] = ds.vecs[ind[1][k] - 1];
      }
      vec3f[4] bezier_temp = void;
      void setup_row(float v) {
        bezier2(v, input[0..4], &bezier_temp[0]);
        bezier2(v, input[4..8], &bezier_temp[1]);
        bezier2(v, input[8..12], &bezier_temp[2]);
        bezier2(v, input[12..16], &bezier_temp[3]);
      }
      void bezier3(float u, vec3f* dest) {
        bezier2(u, bezier_temp[], dest);
      }
      alias subdiv = 256;
      int subdivp = subdiv + 1;
      if (!temp.ptr) temp = new vec3f[subdivp * subdivp];
      int k;
      for (int y = 0; y < subdivp; ++y) {
        float v = y * 1.0 / subdiv;
        setup_row(v);
        for (int x = 0; x < subdivp; ++x) {
          float u = x * 1.0 / subdiv;
          bezier3(u, &temp[k++]);
        }
      }
      vec3f get(int x, int y) { return temp[x * subdivp + y]; }
      int x, y;
      while (x, y) <- cross (0..subdiv, 0..subdiv) {
        float u = x * 1.0 / subdiv, v = y * 1.0 / subdiv;
        int x2, y2;
        vec3f[4] quad = void;
        float[4] angles = void;
        int l;
        while ((x2, y2), l) <- zip([for id <- [0, 1, 3, 2]: (cross (0..2, 0..2))[id]], 0..4) {
          quad[l] = get(x2 + x, y2 + y);
          int xshift = 1, yshift = 1;
          if (u > 0.5) xshift = -1;
          if (v > 0.5) yshift = -1;
          auto normal = vcross(
            get(x2 + x + xshift, y2 + y) - quad[l],
            get(x2 + x, y2 + y + yshift) - quad[l]
          );
          if ((u > 0.5 || v > 0.5) && !(u > 0.5 && v > 0.5))
            normal = vec3f(-normal[0], -normal[1], -normal[2]);
          auto angle = vdot(vnormal(normal), vnormal(vec3f(0.6, 0.3, -1)));
          if (angle < 0) angle = -angle;
          angles[l] = angle;
        }
        while int i <- 0..4 { data ~= vec3f(angles[i]); data ~= quad[i]; entries ++; }
        vertices += 4;
      }
    }
    glBindBufferARB(GL_ARRAY_BUFFER_ARB, teaObj);
    glBufferDataARB(GL_ARRAY_BUFFER_ARB, (size-of vec3f) * data.length, data.ptr, GL_STATIC_DRAW_ARB);
  }
  glEnableClientState GL_COLOR_ARRAY;
  glEnableClientState GL_VERTEX_ARRAY;
  glBindBufferARB(GL_ARRAY_BUFFER_ARB, teaObj);
  glColorPointer(3, GL_FLOAT, 2 * size-of vec3f, void*: 0);
  glVertexPointer(3, GL_FLOAT, 2 * size-of vec3f, void*: size-of vec3f);
  // writeln "Render $entries entries. ";
  glDrawArrays (GL_QUADS, 0, entries);
  SDL_GL_SwapBuffers();
  fps ++;
  auto ct = time(time_t*:null);
  if ct != last_time {
    last_time = ct;
    writeln "FPS: $fps, vertices per scene $vertices";
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
  needUpdate = true;
  
  auto ds = parse "newell_teaset/teapot";
  SDL_Init (SDL_INIT_VIDEO);
  auto flags = SDL_OPENGL | SDL_GL_DOUBLEBUFFER | SDL_RESIZABLE;
  SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
  auto surf = SDL_SetVideoMode (640, 480, 0, flags);
  if !surf quit(1);
  initGL;
  // IMPORTANT: init gl FIRST
  glGenBuffersARB (1, &teaObj);
  resizeWindow (640, 480);
  while true {
    drawScene(ds);
    if update(surf) quit(0);
  }
}
