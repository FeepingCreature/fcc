module smtest;

import glsetup, opengl, libgd, simplex, std.file, std.c.math, std.time;

int fps;
long last_time;

float t = 0;

GLuint tex1, tex2;

struct Block {
  bool active;
}

alias BlockType = Block;

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
  BlockType[16][16][16] cache;
}

class SectorCache {
  Sector[] sectors;
  BlockType delegate(vec3i) dg;
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
  BlockType lookup(vec3i v) {
    for auto sec <- sectors {
      if (sec.contains v) {
        return (v - sec.base).(sec.cache[x][y][z]);
      }
    }
    vec3i low = v & 0xf;
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
  
  glScalef (0.2 x 3);
  glTranslatef (0, 2 * sinf(t / 64), 0);
  BlockType mkBlock(bool b) {
    BlockType res; res.active = b; return res;
  }
  BlockType genFun(vec3i vi) {
    float max(float a, float b) { if (a > b) return a; else return b; }
    float abs(float f) { if (f < 0) return -f; return f; }
    auto dist = max(max(abs(vi.x), abs(vi.y)), abs(vi.z));
    dist -= noise3(vi * 0.1) * 5;
    if dist > 7 return mkBlock(false);
    // if dist < 4 return false;
    
    return mkBlock(true);
  }
  if (!sc) sc = new SectorCache null;
  sc.dg = &genFun;
  auto fun = &sc.lookup;
  bool occluded(vec3i vi) {
    if (!fun(vi).active) return false;
    return eval
      fun vec3i(vi.(x+1, y, z)).active && fun vec3i(vi.(x-1, y, z)).active &&
      fun vec3i(vi.(x, y+1, z)).active && fun vec3i(vi.(x, y-1, z)).active &&
      fun vec3i(vi.(x, y, z+1)).active && fun vec3i(vi.(x, y, z-1)).active;
  }
  while auto vec ← [for x ← cross (-12 .. 12) x 3: vec3i(x)] if fun(vec).active && !occluded(vec) using glMatrix {
    if (noise3(vec3f(vec.(x, y, z)) * 0.3) > 0.5) glBindTexture (GL_TEXTURE_2D, tex1);
    else glBindTexture (GL_TEXTURE_2D, tex2);
    glTranslatef vec;
    auto corners = [for tup <- cross([-1, 1], [-1, 1], [-1, 1]): vec3i(tup)];
  }
  swap();
  fps ++;
  auto ct = µsec();
  if ct > last_time + 1_000_000 {
    last_time = ct;
    writeln "FPS: $fps";
    fps = 0;
  }
}

int loadTexture(string name) {
  GLuint tex;
  auto pngdata = readAll name;
  writeln "mew $(pngdata)";
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
  gl-context-callbacks ~= delegate void() {
    writeln "load textures";
    tex1 = loadTexture "letter-a.png";
    tex2 = loadTexture "letter-b.png";
    writeln "loaded";
  };
  auto surf = setup-gl();
  while true {
    drawScene();
    if update(surf) quit(0);
  }
}
