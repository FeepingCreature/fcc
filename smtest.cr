module smtest;

import glsetup, opengl, libgd, simplex, std.file, std.c.math, std.c.time;

int fps, last_time;

float t = 0;

GLuint tex1, tex2;

class Sector {
  vec3i base;
  bool contains(vec3i v) {
    if (v.x < base.x) return false;
    if (v.y < base.y) return false;
    if (v.z < base.z) return false;
    if (v.x >= base.x + 16) return false;
    if (v.y >= base.y + 16) return false;
    if (v.z >= base.z + 16) return false;
    return true;
  }
  bool[16][16][16] cache;
}

class SectorCache {
  Sector[] sectors;
  bool delegate(vec3i) dg;
  void init(type-of dg dg2) {
    this.dg = dg2;
  }
  Sector calcSector(vec3i base) {
    auto sec = new Sector;
    sec.base = base;
    writeln "calc $(base)";
    int i;
    for (int x, int y, int z) <- cross(0..16, 0..16, 0..16) {
      sec.cache[x][y][z] = dg(base + vec3i(x, y, z));
      i++;
    }
    writeln "done $i";
    return sec;
  }
  bool lookup(vec3i v) {
    for auto sec <- sectors {
      if (sec.contains v)
        return (v - sec.base).(sec.cache[x][y][z]);
    }
    vec3i low;
    if (v.x < 0) low.x = 16 - (-v.x & 0xf);
    else low.x = v.x & 0xf;
    if (v.y < 0) low.y = 16 - (-v.y & 0xf);
    else low.y = v.y & 0xf;
    if (v.z < 0) low.z = 16 - (-v.z & 0xf);
    else low.z = v.z & 0xf;
    auto sec = calcSector (v - low);
    sectors ~= sec;
    return low.(sec.cache[x][y][z]);
  }
}

SectorCache sc;

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
    alias cols = [for i ← 0..8: i / 8.0f];
    alias coords = [(0,0), (0,1), (1,1), (1,0)];
    while (int idx, int count) ← zip ([
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
  void prepareCube() {
    glEnableClientState GL_VERTEX_ARRAY;
    glEnableClientState GL_COLOR_ARRAY;
    glEnableClientState GL_TEXTURE_COORD_ARRAY;
    glColorPointer (3, GL_FLOAT, size-of cubetype, void*:&cubedata[0][0]);
    glVertexPointer (3, GL_FLOAT, size-of cubetype, void*:&cubedata[0][1]);
    glTexCoordPointer (2, GL_FLOAT, size-of cubetype, void*:&cubedata[0][2]);
  }
  void drawCube() {
    glDrawArrays (GL_QUADS, 0, cubedata.length);
  }
  
  glScalef (0.2 x 3);
  glTranslatef (0, 2 * sinf(t / 64), 0);
  bool genFun(vec3i vi) {
    float max(float a, float b) { if (a > b) return a; else return b; }
    float abs(float f) { if (f < 0) return -f; return f; }
    auto dist = max(max(abs(vi.x), abs(vi.y)), abs(vi.z));
    dist -= noise3(vi * 0.1) * 5;
    if dist > 7 return false;
    // if dist < 4 return false;
    
    return true;
  }
  if (!sc) sc = new SectorCache null;
  sc.dg = &genFun;
  auto fun = &sc.lookup;
  bool occluded(vec3i vi) {
    if (!fun(vi)) return false;
    return eval
      fun vec3i(vi.(x+1, y, z)) && fun vec3i(vi.(x-1, y, z)) &&
      fun vec3i(vi.(x, y+1, z)) && fun vec3i(vi.(x, y-1, z)) &&
      fun vec3i(vi.(x, y, z+1)) && fun vec3i(vi.(x, y, z-1));
  }
  prepareCube();
  while auto vec ← [for x ← cross (-12 .. 12) x 3: vec3i(x)] if fun(vec) && !occluded(vec) using glMatrix {
    if (noise3(vec3f(vec.(x, y, z)) * 0.3) > 0.5) glBindTexture (GL_TEXTURE_2D, tex1);
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
  writeln "Read $(pngdata.length), is $((img.sx, img.sy)). Truecolor? $(img.trueColor). ";
  glGenTextures(1, &tex);
  glBindTexture(GL_TEXTURE_2D, tex);
  int[auto~] data;
  while auto pt <- cross img.(0..sy, 0..sx) {
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
  resizeWindow (640, 480);
  tex1 = loadTexture "letter-a.png";
  tex2 = loadTexture "letter-b.png";
  while true {
    drawScene();
    if update(surf) quit(0);
  }
}
