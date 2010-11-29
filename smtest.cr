module smtest;

import glsetup, opengl, libgd, simplex, std.file, std.c.math, std.c.time;

int fps, last_time;

float t = 0;

GLuint tex1, tex2;

void drawScene() {
  glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  glTranslatef (0, 0, -6);
  // glRotatef (t, 1, 0.1, 0);
  // glRotatef (180, 1, 0, 0);
  glRotatef (t, 0, 1, 0);
  t -= 1;
  alias cubetype = (vec3f, vec3f, vec2f);
  cubetype[auto~] cubedata;
  onExit cubedata.free;
  void genCubeData() {
    alias points = cross ((0..2) x 3);
    alias cols = [for i ← 0..8: i / 8.0];
    alias coords = [(0,0), (0,1), (1,1), (1,0)];
    static while (int idx, int count) ← zip ([
      0, 1, 3, 2,  4, 5, 7, 6, // top, bottom
      0, 1, 5, 4,  1, 3, 7, 5,  3, 2, 6, 7,  2, 0, 4, 6], 0..-1) { // sides
      cubedata ~= (
        vec3f (cols[idx] x 3),
        vec3f (points[idx]),
        vec2f (coords[count%4])
      );
    }
  }
  genCubeData();
  void drawCube() {
    glEnableClientState GL_VERTEX_ARRAY;
    glEnableClientState GL_COLOR_ARRAY;
    glEnableClientState GL_TEXTURE_COORD_ARRAY;
    glColorPointer (3, GL_FLOAT, size-of cubetype, &cubedata[0][0]);
    glVertexPointer (3, GL_FLOAT, size-of cubetype, &cubedata[0][1]);
    glTexCoordPointer (2, GL_FLOAT, size-of cubetype, &cubedata[0][2]);
    glDrawArrays (GL_QUADS, 0, cubedata.length);
  }
  
  glScalef (0.2 x 3);
  glTranslatef (0, 2 * sin(t / 64), 0);
  bool fun(vec3f v) {
    float max(float a, float b) { if (a > b) return a; else return b; }
    float abs(float f) { if (f < 0) return -f; return f; }
    auto dist = max(max(abs(v.x), abs(v.y)), abs(v.z));
    dist -= noise3(v * 0.3) * 3;
    if dist > 7 return false;
    if dist < 6 return false;
    return true;
  }
  while auto vec ← [for x ← cross (-10 .. 10) x 3: vec3f(x)] if fun(vec) using glMatrix {
    if (noise3(vec * 0.3) > 0.5) glBindTexture (GL_TEXTURE_2D, tex1);
    else glBindTexture (GL_TEXTURE_2D, tex2);
    glTranslatef vec;
    drawCube();
  }
  swap();
  fps ++;
  auto ct = time(null);
  if ct != last_time {
    last_time = ct;
    writeln "FPS: $fps";
    fps = 0;
  }
}

int loadTexture(string name) {
  GLuint tex;
  auto pngdata = readAll name;
  auto img = gdImageCreateFromPngPtr (pngdata.length, pngdata.ptr);
  // writeln "Read $(pngdata.length), is $((img.sx, img.sy)). Truecolor? $(img.trueColor). ";
  glGenTextures(1, &tex);
  glBindTexture(GL_TEXTURE_2D, tex);
  int[auto~] data;
  while auto pt <- cross (0..img.sy, 0..img.sx) {
    data ~= gdImageGetPixel (img, pt);
  }
  // glTexImage2D(GL_TEXTURE_2D, 0, 3, img.sx, img.sy, 0, GL_RGBA, GL_UNSIGNED_BYTE, img.tpixels);
  gluBuild2DMipmaps (GL_TEXTURE_2D, 3, img.sx, img.sy, GL_RGBA, GL_UNSIGNED_BYTE, data.ptr);
  data.free;
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri (GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  return tex;
}

int main(int argc, char** argv) {
  auto surf = setup-gl();
  tex1 = loadTexture "letter-a.png";
  tex2 = loadTexture "letter-b.png";
  while true {
    drawScene();
    if update(surf) quit(0);
  }
}
