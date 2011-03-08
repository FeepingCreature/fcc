module pyramid;

import opengl, glsetup;

interface Camera {
  void gl-setup();
}

class PerspectiveCam : Camera {
  float fov, zNear, zFar, aspect;
  void init() {
    zNear = 0.01f;
    zFar = 100f;
    fov = 45f;
    aspect = 1f;
  }
  void gl-setup() {
    glMatrixMode GL_PROJECTION;
    glLoadIdentity;
    gluPerspective (fov, aspect, zNear, zFar);
  }
}

vec3f cross(vec3f a, vec3f b) { return vec3f(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x); }
vec3f normalized(vec3f v) { return v / v.length; }

import std.c.math;

float angle(vec3f v, vec3f to, vec3f refer) {
  // yay, http://tomyeah.com/signed-angle-between-two-vectors3d-in-cc/
  auto v1 = v.cross(to) * refer;
  bool flipped = eval (v1.sum < 0);
  auto res = acosf((v*to).sum / sqrtf(v.selfdot * to.selfdot));
  // fudge
  if (flipped) res = -res;
  return res;
}

vec3f rotate(vec3f vec, vec3f axis, float angle) using vec {
  float u = axis.x, v = axis.y, w = axis.z;
  float uu = u*u, vv = v*v, ww = w*w;
  float v_w = vv + ww, u_w = uu + ww, u_v = uu + vv;
  float dd = (vec*axis).sum, cosa = cosf(angle), sina = sinf(angle);
  vec3f res = void;
  res.x = u*dd+(x*v_w+u*(v*(-y)+w*(-z))) * cosa + (w*(-y)+v*z) * sina;
  res.y = v*dd+(y*u_w+v*(u*(-x)+w*(-z))) * cosa + (w*x+u*(-z)) * sina;
  res.z = w*dd+(z*u_v+w*(u*(-x)+v*(-y))) * cosa + (v*(-x)+u*y) * sina;
  res /= axis.lensq;
  return res;
}

alias PI = 3.1415926538;
alias PI180 = PI/180.0;

template WorldCam(T) << EOF
  class WorldCam : T {
    vec3f up, pos, lookat;
    alias dir = lookat - pos;
    vec3f setDir(vec3f v) { lookat = pos + v; return lookat; }
    void init() {
      super.init();
      (up, pos) = (vec3f.Y, vec3f(0));
      setDir -vec3f.Z;
    }
    void gl-setup() {
      super.gl-setup();
      glMatrixMode GL_MODELVIEW;
      glLoadIdentity;
      auto dirz = dir;
      dirz.z = -dirz.z;
      auto left = up.cross(dirz).normalized(), up = dirz.cross(left).normalized();
      (vec3f.Y.angle(up, left) / PI180).glRotatef vec3f.X;
      (vec3f.X.angle(left, up) / PI180).glRotatef vec3f.Y;
      glTranslatef (-pos);
    }
  }
EOF

template EgoCam(T) << EOF
  class EgoCam : T {
    vec3f pos;
    float turnX, turnY;
    void init() {
      (pos, turnX, turnY) = (vec3f(0), 0, 0);
      super.init();
    }
    void turn-left(float f) { turnX += f; }
    alias lowlimit = -PI / 2 + 0.1;
    alias highlimit = PI / 2 - 0.1;
    void turn-up(float f) { turnY -= f; if (turnY < lowlimit) turnY = lowlimit; if (turnY > highlimit) turnY = highlimit; }
    alias dir = vec3f.Z.rotate(vec3f.X, turnY).rotate(vec3f.Y, turnX);
    alias left = vec3f.Y.cross(dir).normalized();
    void gl-setup() {
      super.gl-setup();
      glMatrixMode GL_MODELVIEW;
      glLoadIdentity;
      auto dirz = dir; dirz.z = -dirz.z;
      auto left = vec3f.Y.cross(dirz).normalized(), up = dirz.cross(left).normalized();
      (vec3f.Y.angle(up, left) / PI180).glRotatef vec3f.X;
      (vec3f.X.angle(left, up) / PI180).glRotatef vec3f.Y;
      glTranslatef (-pos);
    }
  }
EOF

import sdl;

void main() {
  auto surf = setup-gl();
  resizeWindow (640, 480);
  int t;
  void dividePyramid(vec3f[4]* pCorners, void delegate(vec3f[4]*) callback) {
    vec3f half(int a, int b) { return ((*pCorners)[a] + (*pCorners)[b]) * 0.5; }
    vec3f idx(int i) { return (*pCorners)[i]; } // lol
    vec3f[4] temp = void;
    temp = [idx 0, half (0, 1), half (0, 2), half (0, 3)]; callback &temp;
    temp = [idx 1, half (1, 2), half (1, 0), half (1, 3)]; callback &temp;
    temp = [idx 2, half (2, 0), half (2, 1), half (2, 3)]; callback &temp;
    temp = [idx 3, half (0, 3), half (1, 3), half (2, 3)]; callback &temp;
  }
  auto ec = new EgoCam!PerspectiveCam;
  ec.init();
  ec.pos = vec3f(0, 0, -3);
  ec.turnX = 0;
  auto vertices = [vec3f (-1, -0.6f, -1), vec3f (1, -0.6f, -1), vec3f (0, -0.6f, 1), vec3f (0, 1.0f, 0)];
  void rootFun(vec3f[4]* pVecs) {
    alias vecs = *pVecs;
    using opengl.Triangles {
      for (int i, int id) <- zip (0..-1, [0, 1, 3,  1, 2, 3,  2, 0, 3,  0, 2, 1]) {
        auto vec = vecs[id];
        glColor3f (vec + vec3f(1, 0.6, 0.3) * (i / 12f));
        glVertex3f vec;
      }
    }
  }
  auto curFun = &rootFun;
  for 0..6
    curFun = new delegate void(vec3f[4]* pVecs) { dividePyramid(pVecs, curFun); };
  auto pyrlist = glGenLists(1);
  onSuccess pyrlist.glDeleteLists(1);
  {
    pyrlist.glNewList GL_COMPILE;
    onSuccess glEndList;
    curFun (&vertices);
  }
  // SDL_WM_GrabInput(SDL_GRAB_ON);
  SDL_WarpMouse(320, 240);
  if surf.update() quit(0);
  SDL_ShowCursor(false);
  while true {
    glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    ec.aspect = surf.w * 1f / surf.h;
    ec.gl-setup();
    // glRotatef (t++, 0, 1, 0);
    pyrlist.glCallList();
    if surf.update() quit(0);
    auto idelta = mousepos - vec2i(320, 240);
    auto delta = vec2f((0.001 * idelta).(x, y));
    using (ec, delta) { turn-left-x; turn-up-y; } // *MWAHAHAHAHAAAAAHAHA*
    if idelta.x || idelta.y
      SDL_WarpMouse(320, 240);
    
    alias movestep = 0.014;
    if (keyPressed[SDLK_w]) ec.pos += ec.dir * movestep;
    if (keyPressed[SDLK_s]) ec.pos -= ec.dir * movestep;
    if (keyPressed[SDLK_a]) ec.pos += ec.left * movestep;
    if (keyPressed[SDLK_d]) ec.pos -= ec.left * movestep;
  }
}
