module smtest;

import glsetup, opengl, libgd, simplex, std.file, std.c.math, std.time;

int fps;
long last_time;

float t = 0;

GLuint tex1, tex2;

struct Block {
  bool active;
  int lightlevel;
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
  // does not cause calcs
  BlockType weakLookup(vec3i v, BlockType deflt) {
    for auto sec <- sectors if sec.contains v {
      return (v - sec.base).(sec.cache[x][y][z]);
    }
    return deflt;
  }
}

void initLight(SectorCache sc) {
  Sector[auto~] tops;
  onSuccess tops.free;
  for (auto sector <- sc.sectors) {
    bool replaced;
    for (int i <- 0..tops.length) {
      if (!replaced
       && tops[i].base.(x == sector.base.x && z == sector.base.z)
       && tops[i].base.y < sector.base.y) { // found a higher one
        tops[i] = sector;
        replaced = true;
      }
    }
    if (!replaced) tops ~= sector;
  }
  for (auto sector <- tops) { // fill top with light
    for (int x, int z) <- cross(0..16, 0..16) {
      sector.cache[x][15][z].lightlevel = 64;
    }
  }
}

void stepLight(SectorCache sc) {
  BlockType nothing;
  for (auto sector <- sc.sectors) {
    for auto vec <- [for tup <- cross(0..16, 0..16, 0..16): vec3i(tup)] {
      int sum;
      auto mybase = sector.base + vec;
      for auto vec2 <- [for tup <- cross([-1, 0, 1], [-1, 0, 1]): vec2i(tup)] {
        auto bt = sc.weakLookup(mybase + vec3i(vec2.x, 1, vec2.y), nothing);
        if bt.active bt.lightlevel = 0; // shadows
        sum += bt.lightlevel;
      }
      sum /= 9;
      sector.cache[vec.x][vec.y][vec.z].lightlevel = sum;
    }
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
  glTranslatef (0, 4 * sinf(t / 64), 0);
  BlockType mkBlock(bool b) {
    BlockType res; res.active = b; return res;
  }
  BlockType genFun(vec3i vi) {
    float max(float a, float b) { if (a > b) return a; else return b; }
    float abs(float f) { if (f < 0) return -f; return f; }
    
    // int sum = vi.((eval abs x < 2) + (eval abs y < 2) + (eval abs z < 2));
    // return mkBlock eval sum > 1; // axis cross test shape
    
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
    auto corners = [for tup <- cross([0, 1], [0, 1], [0, 1]): vec3i(tup)];
    auto sides = [
      ([0, 1, 3, 2], -vec3i.X),
      ([4, 6, 7, 5],  vec3i.X),
      ([1, 5, 7, 3],  vec3i.Z),
      ([0, 2, 6, 4], -vec3i.Z),
      ([2, 3, 7, 6],  vec3i.Y),
      ([1, 0, 4, 5], -vec3i.Y)
    ];
    using Quads {
      for (int[4] points, vec3i dir) <- sides {
        auto bt = fun(vec + dir);
        glColor3f vec3f(bt.lightlevel / 64f);
        for int point <- points {
          glVertex3f vec3f(corners[point]);
        }
      }
    }
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
    initLight sc;
    stepLight sc;
    if update(surf) quit(0);
  }
}
