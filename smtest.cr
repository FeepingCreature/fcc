module smtest;

import glsetup, opengl, libgd, simplex, std.file, std.math, std.time, std.thread, sdl;

int fps;
long last_time;
float calcsum = 0;
float lightsum = 0;

GLuint tex1, tex2;

struct Block {
  bool active;
  int lightlevel;
}

alias BlockType = Block;

alias SectorSize = 16;

class Sector {
  vec3i base;
  bool contains(vec3i v) {
    v -= base;
    return eval v.(
      x >= 0 && y >= 0 && z >= 0 &&
      x < SectorSize && y < SectorSize && z < SectorSize
    );
  }
  BlockType[SectorSize][SectorSize][SectorSize] cache;
  void init() { }
  void init(Sector s) { base = s.base; cache = s.cache; }
}

class SectorCache {
  Sector[auto~] sectors, backup;
  bool backupIsInited;
  Sector[] getBackup(bool initIt = false) {
    if backup.length != sectors.length {
      backup.free;
      backup = new Sector[sectors.length];
      backupIsInited = false;
    }
    if (initIt || !backupIsInited) {
      for int i <- 0..sectors.length {
        if (!backup[i]) backup[i] = new Sector;
        backup[i].init sectors[i];
      }
      backupIsInited = true;
    }
    return backup[];
  }
  void swapBackup() { (sectors, backup) = (backup, sectors); }
  BlockType delegate(vec3i) dg;
  Mutex m;
  void init(type-of dg dg2) {
    dg = dg2;
    m = new Mutex;
  }
  Sector calcSector(vec3i base) {
    auto sec = new Sector;
    sec.base = base;
    writeln "calc $(base)";
    int i;
    for (int x, int y, int z) <- cross((0..SectorSize) x 3) {
      sec.cache[x][y][z] = dg(base + vec3i(x, y, z));
      i++;
    }
    writeln "done $i";
    return sec;
  }
  int lastMatched;
  BlockType lookup(vec3i v) {
    alias last = sectors[lastMatched];
    if sectors.length && last.contains v {
      auto sec = last;
      return (v - sec.base).(sec.cache[x][y][z]);
    }
    for (int id, Sector sec) <- zip(0..-1, sectors) {
      if (sec.contains v) {
        lastMatched = id;
        return (v - sec.base).(sec.cache[x][y][z]);
      }
    }
    vec3i low = (v & 0x7fff_ffff) % SectorSize;
    auto sec = calcSector (v - low);
    sectors ~= sec;
    return low.(sec.cache[x][y][z]);
  }
  // does not cause calcs
  BlockType weakLookup(vec3i v, BlockType deflt, bool inBackup = false) {
    auto list = sectors;
    if (inBackup) list = backup;
    if !list.length return deflt;
    if lastMatched < list.length && (auto sec = list[lastMatched]).contains v {
      return (v - sec.base).(sec.cache[x][y][z]);
    }
    for (int id, Sector sec) <- zip(0..-1, list) if id != lastMatched && sec.contains v {
      lastMatched = id;
      return (v - sec.base).(sec.cache[x][y][z]);
    }
    return deflt;
  }
}

void initLight(SectorCache sc) {
  Sector[] list;
  using autoLock sc.m list = sc.getBackup(initIt => true);
  Sector[auto~] tops;
  onSuccess tops.free;
  for (auto sector <- list) {
    bool replaced;
    for (int i <- 0..tops.length) {
      if (!replaced
       && tops[i].base.xz == sector.base.xz
       && tops[i].base.y < sector.base.y) { // found a higher one
        tops[i] = sector;
        replaced = true;
      }
    }
    if (!replaced) tops ~= sector;
  }
  for (auto sector <- tops) { // fill top with light
    for (int x, int z) <- cross(0..SectorSize, 0..SectorSize) {
      sector.cache[x][SectorSize - 1][z].lightlevel = 128;
    }
  }
}

void stepLight(SectorCache sc) {
  BlockType nothing;
  Sector[] list;
  using autoLock sc.m list = sc.getBackup();
  for (auto sector <- list) {
    for auto vec <- [for tup <- cross((0..SectorSize) x 3): vec3i(tup)] {
      alias myBlock = vec.(sector.cache[x][y][z]);
      if !myBlock.active {
        int sum;
        auto mybase = sector.base, fullvec = mybase + vec;
        for auto vec2 <- [for tup <- cross([-1, 0, 1], [1], [-1, 0, 1]): vec3i(tup)] {
          auto nuvec = fullvec + vec2;
          BlockType bt = void;
          if sector.contains nuvec {
            bt = (vec + vec2).(sector.cache[x][y][z]);
          } else bt = sc.weakLookup(nuvec, nothing, inBackup => true);
          if bt.active bt.lightlevel = 0; // shadows
          sum += bt.lightlevel;
        }
        sum /= 9;
        myBlock.lightlevel = sum;
      }
    }
  }
  using autoLock sc.m sc.swapBackup;
}

import camera;

Camera cam;

void drawScene(SectorCache* scp) {
  alias sc = *scp;
  glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  cam.gl-setup();
  
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
  sc.m.lock;
  onExit (*scp).m.unlock;
  sc.dg = &genFun;
  auto fun = &sc.lookup;
  bool occluded(vec3i vi) {
    if (!fun(vi).active) return false;
    return eval
      fun vec3i(vi.(x+1, y, z)).active && fun vec3i(vi.(x-1, y, z)).active &&
      fun vec3i(vi.(x, y+1, z)).active && fun vec3i(vi.(x, y-1, z)).active &&
      fun vec3i(vi.(x, y, z+1)).active && fun vec3i(vi.(x, y, z-1)).active;
  }
  
  vec3f[4][auto~][2] colorCache;
  vec3f[4][auto~][2] vertexCache;
  vec2f[4][auto~][2] texcoordCache;
  void flushCache(int tex = -1) {
    int from, to;
    if (tex == -1) (from, to) = (0, 2);
    else (from, to) = (tex, tex + 1);
    for (int tid <- from .. to) {
      if (tid == 0) glBindTexture (GL_TEXTURE_2D, tex1);
      else glBindTexture (GL_TEXTURE_2D, tex2);
      glEnableClientState GL_VERTEX_ARRAY;
      glEnableClientState GL_COLOR_ARRAY;
      glEnableClientState GL_TEXTURE_COORD_ARRAY;
      glColorPointer(3, GL_FLOAT, size-of vec3f, void*:colorCache[tid].ptr);
      glVertexPointer(3, GL_FLOAT, size-of vec3f, void*:vertexCache[tid].ptr);
      glTexCoordPointer(2, GL_FLOAT, size-of vec2f, void*:texcoordCache[tid].ptr);
      glDrawArrays(GL_QUADS, 0, 4 * vertexCache[tid].length);
      glDisableClientState GL_VERTEX_ARRAY;
      glDisableClientState GL_COLOR_ARRAY;
      glDisableClientState GL_TEXTURE_COORD_ARRAY;
      colorCache[tid].free;
      vertexCache[tid].free;
      texcoordCache[tid].free;
    }
  }
  void queueQuad(int tex, vec3f color, vec3f[4] corners) {
    colorCache[tex] ~= [color, color, color, color];
    vertexCache[tex] ~= corners;
    texcoordCache[tex] ~= [vec2f(0, 0), vec2f(0, 1), vec2f(1, 1), vec2f(1, 0)];
    if (vertexCache[tex].length == 4096) flushCache(tex);
  }
  
  auto start = sec();
  while auto vec ← [for x ← cross (-12 .. 12) x 3: vec3i(x)] if fun(vec).active && !occluded(vec) {
    int tex;
    if (noise3(vec3f(vec.(x, y, z)) * 0.3) > 0.5) tex = 0;
    else tex = 1;
    alias corners = [for tup <- cross([0, 1], [0, 1], [0, 1]): vec3i(tup)];
    auto sides = [
      ([0, 1, 3, 2], -vec3i.X),
      ([4, 6, 7, 5],  vec3i.X),
      ([1, 5, 7, 3],  vec3i.Z),
      ([0, 2, 6, 4], -vec3i.Z),
      ([2, 3, 7, 6],  vec3i.Y),
      ([1, 0, 4, 5], -vec3i.Y)
    ];
    for (int[4] points, vec3i dir) <- sides {
      auto bt = fun(vec + dir);
      alias map = [for point <- points: vec3f(corners[point]) + vec];
      if !bt.active
        queueQuad (
          tex,
          vec3f(bt.lightlevel / 64f),
          [map[0], map[1], map[2], map[3]]
        );
    }
  }
  flushCache();
  swap();
  calcsum += float:(sec() - start);
  fps ++;
  auto ct = µsec();
  if ct > last_time + 1_000_000 {
    last_time = ct;
    writeln "FPS: $fps, $(calcsum)s for calc, $(lightsum)s for light";
    fps = 0;
    calcsum = 0;
    lightsum = 0;
  }
}

int loadTexture(string pngdata) {
  GLuint tex;
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
  auto ec = new EgoCam!PerspectiveCam (vec3f(0, 0, -32), 0, 0);
  ec.fov = 60f;
  cam = ec;
  gl-context-callbacks ~= delegate void() {
    writeln "load textures";
    tex1 = loadTexture import("letter-a.png");
    tex2 = loadTexture import("letter-b.png");
    // tex1 = loadTexture import("smooth-rock-tex0-32.png");
    // tex2 = loadTexture import("vivid-rock-tex-32.png");
    writeln "loaded";
  };
  auto surf = setup-gl();
  gl-context-callbacks ~= delegate void() {
    ec.aspect = surf.w * 1f / surf.h;
  };
  bool active;
  void toggleActive() {
    SDL_ShowCursor active;
    if !active
      // SDL_WM_GrabInput(SDL_GRAB_ON);
      SDL_WarpMouse(320, 240);
    active = eval !active;
  }
  auto lastTime = sec();
  auto tp = new ThreadPool 1;
  SectorCache sc;
  drawScene &sc; // init sector cache
  tp.addTask delegate void() {
    while true {
      initLight sc;
      stepLight sc;
    }
  };
  while true {
    drawScene &sc;
    /*auto start = sec();
    initLight sc;
    stepLight sc;
    lightsum += float:(sec() - start);*/
    if update(surf) quit(0);
    
    // copied from pyramid.cr
    if (active) {
      auto idelta = mousepos - vec2i(320, 240);
      auto delta = vec2f((0.001 * idelta).(x, y));
      using (ec, delta) { turn-left-x; turn-up-y; } // *MWAHAHAHAHAAAAAHAHA*
      if idelta.x || idelta.y
        SDL_WarpMouse(320, 240);
    }
    if (mouseClicked) toggleActive;
    
    auto factor = float:(sec() - lastTime);
    auto wsfactor = factor * 16, adfactor = factor * 64;
    lastTime = sec();
    using ec {
      if (keyPressed[SDLK_w]) pos += dir.normalize3f() * wsfactor;
      if (keyPressed[SDLK_s]) pos -= dir.normalize3f() * wsfactor;
      if (keyPressed[SDLK_a]) pos += left.normalize3f() * adfactor;
      if (keyPressed[SDLK_d]) pos -= left.normalize3f() * adfactor;
    }
  }
}
