module pyramid;

import opengl, glsetup;

import sdl, camera;

void main(string[] args) {
  // resizeWindow (640, 480);
  auto vertices = [vec3f (-1, -1, -1), vec3f(1, 1, 1)];
  void dividePyramid(vec3f[vertices.length]* pCorners, void delegate(vec3f[vertices.length]*) callback) {
    auto a = (*pCorners)[0], b = (*pCorners)[1];
    for auto v <- [for tup <- cross (0..3, 0..3, 0..3): vec3i(tup)] {
      int bsum = eval(v.x == 1) + eval(v.y == 1) + eval(v.z == 1);
      if bsum < 2 {
        vec3f[2] temp = [a * (3 - v) / 3f + b * (v + 0) / 3f,
                         a * (2 - v) / 3f + b * (v + 1) / 3f];
        callback &temp;
      }
    }
  }
  auto ec = new EgoCam!PerspectiveCam (vec3f(0, 0, -3), 0, 0);
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
  {
    int res;
    SDL_GL_GetAttribute(SDL_GL_DOUBLEBUFFER, &res);
    writeln "0 or 1, enable or disable double buffering: $(res)";
    prefix SDL_GL_ for (int num, string info) <- [
      (RED_SIZE,         "framebuffer red component"),
      (GREEN_SIZE,       "framebuffer green component"),
      (BLUE_SIZE,        "framebuffer blue component"),
      (ALPHA_SIZE,       "framebuffer alpha component"),
      (BUFFER_SIZE,      "framebuffer"),
      (DEPTH_SIZE,       "depth buffer"),
      (STENCIL_SIZE,     "stencil buffer"),
      (ACCUM_RED_SIZE,   "accumulation buffer red component"),
      (ACCUM_GREEN_SIZE, "accumulation buffer green component"),
      (ACCUM_BLUE_SIZE,  "accumulation buffer blue component"),
      (ACCUM_ALPHA_SIZE, "accumulation buffer alpha component")]
    {
      SDL_GL_GetAttribute(num, &res);
      writeln "Size of the $info, in bits: $res";
    }
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
