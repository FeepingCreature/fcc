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

import std.c.math;

vec3f cross3f(vec3f a, vec3f b) { return a.yzx * b.zxy - a.zxy * b.yzx; }

vec3f normalize3f(vec3f v) { return v / v.length; }

float angle3f(vec3f v, vec3f to, vec3f refer) {
  // yay, http://tomyeah.com/signed-angle-between-two-vectors3d-in-cc/
  auto v1 = v.cross3f(to) * refer;
  bool flipped = eval (v1.sum < 0);
  auto res = acosf((v*to).sum / sqrtf(v.selfdot * to.selfdot));
  // fudge
  if (flipped) res = -res;
  return res;
}

vec3f rotate3f(vec3f vec, vec3f axis, float angle) using vec {
  float u = axis.x, v = axis.y, w = axis.z;
  float uu = u*u, vv = v*v, ww = w*w;
  float v_w = vv + ww, u_w = uu + ww, u_v = uu + vv;
  float dd = (vec*axis).sum, cosa = cosf(angle), sina = sinf(angle);
  vec3f res = void;
  // pathologically slow to parse
  /*res = axis * dd
    + (vec * vec3f(v_w, u_w, u_v) + axis * (axis.yxx*(-vec.yxx) + axis.zzy * (-vec.zzy))) * cosa
    + (axis.zzy * vec3f (vec.(-y, x, -x)) + axis.yxx * vec3f(vec.(z, -z, y))) * sina;*/
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
      auto left = up.cross3f(dirz).normalize3f(), up = dirz.cross3f(left).normalize3f();
      (vec3f.Y.angle3f(up, left) / PI180).glRotatef vec3f.X;
      (vec3f.X.angle3f(left, up) / PI180).glRotatef vec3f.Y;
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
    alias dir = vec3f.Z.rotate3f(vec3f.X, turnY).rotate3f(vec3f.Y, turnX);
    alias left = vec3f.Y.cross3f(dir).normalize3f();
    void gl-setup() {
      super.gl-setup();
      glMatrixMode GL_MODELVIEW;
      glLoadIdentity;
      auto dirz = dir; dirz.z = -dirz.z;
      auto left = vec3f.Y.cross3f(dirz).normalize3f(), up = dirz.cross3f(left).normalize3f();
      (vec3f.Y.angle3f(up, left) / PI180).glRotatef vec3f.X;
      (vec3f.X.angle3f(left, up) / PI180).glRotatef vec3f.Y;
      glTranslatef (-pos);
    }
  }
EOF

import sdl;

void main(string[] args) {
  // resizeWindow (640, 480);
  writeln "_ebp is $(_ebp)";
  int t;
  // auto vertices = [vec3f (-1, -0.6f, -1), vec3f (1, -0.6f, -1), vec3f (0, -0.6f, 1), vec3f (0, 1.0f, 0)];
  auto vertices = [vec3f (-1, -1, -1), vec3f(1, 1, 1)];
  void dividePyramid(vec3f[vertices.length]* pCorners, void delegate(vec3f[vertices.length]*) callback) {
    auto a = (*pCorners)[0], b = (*pCorners)[1];
    for (int x, int y, int z) <- cross (0..3, 0..3, 0..3) {
      int bsum = eval(x == 1) + eval(y == 1) + eval(z == 1);
      if bsum < 2 {
        vec3f[2] temp = [
          vec3f(
            a.x * (3-x)/3f + b.x * x/3f,
            a.y * (3-y)/3f + b.y * y/3f,
            a.z * (3-z)/3f + b.z * z/3f
          ),
          vec3f(
            a.x * (2-x)/3f + b.x * (x + 1)/3f,
            a.y * (2-y)/3f + b.y * (y + 1)/3f,
            a.z * (2-z)/3f + b.z * (z + 1)/3f
          )
        ];
        callback &temp;
      }
    }
    /*
    vec3f[vertices.length] temp = void;
    temp = [idx 0, half (0, 1), half (0, 2), half (0, 3)]; callback &temp;
    temp = [idx 1, half (1, 2), half (1, 0), half (1, 3)]; callback &temp;
    temp = [idx 2, half (2, 0), half (2, 1), half (2, 3)]; callback &temp;
    temp = [idx 3, half (0, 3), half (1, 3), half (2, 3)]; callback &temp;*/
  }
  auto ec = new EgoCam!PerspectiveCam;
  ec.init();
  ec.pos = vec3f(0, 0, -3);
  ec.turnX = 0;
  bool pass;
  vec3f[auto~] vertexQuadData, colorQuadData;
  int[auto~] vertexIndexData;
  void addVertex(vec3f pos, vec3f col) {
    auto limit = vertexQuadData.length - 64;
    if (limit < 0) limit = 0;
    for (int i = vertexQuadData.length - 1; i >= limit; --i) {
      if (vertexQuadData[i] == pos) { vertexIndexData ~= i; return; }
    }
    vertexIndexData ~= vertexQuadData.length;
    vertexQuadData ~= pos;
    colorQuadData ~= col;
  }
  void rootFun(vec3f[vertices.length]* pVecs) {
    alias twoVecs = *pVecs;
    auto vecs = [for tup <- cross(0..2, 0..2, 0..2): vec3f(twoVecs[tup[0]].x, twoVecs[tup[1]].y, twoVecs[tup[2]].z)];
    for (int i, int id) <- zip (0..-1, [0, 1, 3, 2,  2, 3, 7, 6,  6, 7, 5, 4,  4, 5, 1, 0,  1, 5, 7, 3,  2, 6, 4, 0]) {
      auto vec = vecs[id];
      // glColor3f (vec + vec3f(1, 0.6, 0.3) * (i / 18f));
      // glVertex3f vec;
      // vertexQuadData ~= vec;
      addVertex (vec, vec + vec3f(1, 0.6, 0.3) * (i / 24f));
    }
  }
  writeln "ebp is $(_ebp)";
  type-of &rootFun mkFun(int depth) {
    auto curFun = &rootFun;
    for 0..depth
      curFun = new delegate void(vec3f[vertices.length]* pVecs) { dividePyramid(pVecs, curFun); };
    return curFun;
  }
  int curDepth = 1;
  GLuint[3] lists;
  void regenList() {
    if (lists[0]) glDeleteBuffersARB(3, lists.ptr);
    glGenBuffersARB(3, lists.ptr);
    vertexQuadData.free; colorQuadData.free;
    vertexIndexData.free;
    writeln "call with $curDepth";
    auto fun = mkFun curDepth;
    writeln "compute";
    fun &vertices;
    writeln "upload $(vertexQuadData.length) vertices, $(vertexIndexData.length) indices. ";
    for (int i, vec3f[] list) <- zip(0..2, [vertexQuadData[], colorQuadData[]]) using GL_ARRAY_BUFFER_ARB {
      glBindBufferARB lists[i];
      glBufferDataARB ((size-of vec3f) * list.length, list.ptr, GL_STATIC_DRAW_ARB);
    }
    glBindBufferARB (GL_ELEMENT_ARRAY_BUFFER_ARB, lists[2]);
    using GL_ELEMENT_ARRAY_BUFFER_ARB {
      glBufferDataARB (4 * vertexIndexData.length, vertexIndexData.ptr, GL_STATIC_DRAW_ARB);
    }
  }
  bool active;
  void toggleActive() {
    if (active) {
      SDL_ShowCursor true;
    } else {
      SDL_ShowCursor false;
      // SDL_WM_GrabInput(SDL_GRAB_ON);
      SDL_WarpMouse(320, 240);
    }
    active = eval !active;
  }
  gl-context-callbacks ~= delegate void() {
    writeln "regenList()";
    regenList();
  };
  auto surf = setup-gl();
  for (int num, string info) <- [
    (SDL_GL_RED_SIZE,         "Size of the framebuffer red component, in bits"),
    (SDL_GL_GREEN_SIZE,       "Size of the framebuffer green component, in bits"),
    (SDL_GL_BLUE_SIZE,        "Size of the framebuffer blue component, in bits"),
    (SDL_GL_ALPHA_SIZE,       "Size of the framebuffer alpha component, in bits"),
    (SDL_GL_DOUBLEBUFFER,     "0 or 1, enable or disable double buffering"),
    (SDL_GL_BUFFER_SIZE,      "Size of the framebuffer, in bits"),
    (SDL_GL_DEPTH_SIZE,       "Size of the depth buffer, in bits"),
    (SDL_GL_STENCIL_SIZE,     "Size of the stencil buffer, in bits"),
    (SDL_GL_ACCUM_RED_SIZE,   "Size of the accumulation buffer red component, in bits"),
    (SDL_GL_ACCUM_GREEN_SIZE, "Size of the accumulation buffer green component, in bits"),
    (SDL_GL_ACCUM_BLUE_SIZE,  "Size of the accumulation buffer blue component, in bits"),
    (SDL_GL_ACCUM_ALPHA_SIZE, "Size of the accumulation buffer alpha component, in bits")] {
    int res;
    SDL_GL_GetAttribute(num, &res);
    writeln "$info: $res";
  }
  while true {
    glClearColor (0 x 3, 0);
    glClearDepth 1;
    glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
    ec.aspect = surf.w * 1f / surf.h;
    ec.gl-setup();
    // glRotatef (t++, 0, 1, 0);
    glEnableClientState GL_VERTEX_ARRAY;
    glEnableClientState GL_COLOR_ARRAY;
    
    GL_ARRAY_BUFFER_ARB.glBindBufferARB lists[0];
    glVertexPointer(3, GL_FLOAT, size-of vec3f, null);
    GL_ARRAY_BUFFER_ARB.glBindBufferARB lists[1];
    glColorPointer(3, GL_FLOAT, size-of vec3f, null);
    GL_ELEMENT_ARRAY_BUFFER_ARB.glBindBufferARB lists[2];
    // glDrawArrays (GL_QUADS, 0, vertexQuadData.length);
    glDrawElements (GL_QUADS, vertexIndexData.length, GL_UNSIGNED_INT, null);
    
    if surf.update() quit(0);
    if (active) {
      auto idelta = mousepos - vec2i(320, 240);
      auto delta = vec2f((0.001 * idelta).(x, y));
      using (ec, delta) { turn-left-x; turn-up-y; } // *MWAHAHAHAHAAAAAHAHA*
      if idelta.x || idelta.y
        SDL_WarpMouse(320, 240);
    }
    if (mouseClicked) toggleActive;
    
    alias movestep = 0.014;
    if (keyPressed[SDLK_w]) ec.pos += ec.dir * movestep;
    if (keyPressed[SDLK_s]) ec.pos -= ec.dir * movestep;
    if (keyPressed[SDLK_a]) ec.pos += ec.left * movestep;
    if (keyPressed[SDLK_d]) ec.pos -= ec.left * movestep;
    if (keyPushed[SDLK_PLUS] || keyPushed[SDLK_KP_PLUS]) { curDepth ++; regenList; }
    if (keyPushed[SDLK_MINUS] || keyPushed[SDLK_KP_MINUS]) { if curDepth curDepth --; regenList; }
  }
}
