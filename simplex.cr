module simplex;

import std.c.fenv, std.c.stdlib;

int[] perm;
int[3][12] grad3;

float dot2(int[3] whee, float a, float b) {
  return whee[0] * a + whee[1] * b;
}

float dot3(int[3] whee, float a, float b, float c) {
  return whee[0] * a + whee[1] * b + whee[2] * c;
}

void permsetup() {
  perm ~= [for 0..256: rand() % 256].eval;
  perm ~= perm;
  int i;
  alias values = [1,1,0,-1, 1,0,1,-1, 0,-1,-1,0, 1,0,1,-1, 0,1,1,0, -1,-1,0,-1, 0,1,1,0, -1,1,0,1, -1,0,-1,-1];
  while ((int k, int l), int idx) ← zip (cross (0..12, 0..3), 0..-1) {
    grad3[k][l] = values[idx];
  }
}

int fastfloor(float f) {
  alias magicdelta = 0.000000015;
  alias roundeps = 0.5 - magicdelta;
  alias magic = 6755399441055744.0;
  // double a = magic, b = magicdelta, c = roundeps;
  // auto ap = int*:&a, bp = int*:&b, cp = int*:&c;
  // writeln "[$(ap[0]),$(ap[1])], [$(bp[0]), $(bp[1])], [$(cp[0]), $(cp[1])]";
  // writeln "c is $c - $(string-of type-of roundeps)";
  double d = f - magicdelta;
  // writeln "$d is $f - $magicdelta";
  d += magic;
  // writeln "+= $magic = $d";
  int res = (int*:&d)[0];
  // writeln "fastfloor of $f is $res";
  return res;
}

float noise2(vec2f f) {
  if !perm.length permsetup;
  alias sqrt3 = sqrtf(3);
  alias f2 = 0.5 * (sqrt3 - 1);
  alias g2 = (3 - sqrt3) / 6;
  auto backup = fegetround();
  onExit fesetround backup;
  fesetround FE_DOWNWARD;
  float[3] n = void;
  
  float s = (f.x + f.y) * f2;
  int i = fastfloor(f.x + s), j = fastfloor(f.y + s);
  
  float t = (i + j) * g2;
  vec2f[3] xy;
  xy[0] = f - (vec2i(i,j) - vec2f(t));
  
  int i1, j1;
  if xy[0].x > xy[0].y i1 = 1;
  else j1 = 1;
  
  {
    auto temp = 1 - 2 * g2;
    xy[1] = xy[0] - vec2i(i1, j1) + vec2f (g2);
    xy[2] = xy[0] - vec2f(temp);
  }
  int ii = i & 255, jj = j & 255;
  
  int[3] gi = void;
  gi[0] = perm[ii + perm[jj]] % 12;
  gi[1] = perm[ii + i1 + perm[jj + j1]] % 12;
  gi[2] = perm[ii + 1  + perm[jj + 1 ]] % 12;
  
  for (int k = 0; k < 3; ++k) {
    float ft = 0.5 - xy[k].x*xy[k].x - xy[k].y*xy[k].y;
    if ft < 0 n[k] = 0;
    else {
      ft = ft * ft;
      n[k] = ft * ft * dot2(grad3[gi[k]], xy[k]);
    }
  }
  return 0.5 + 35 * (n[0] + n[1] + n[2]);
}

void time-it(string t, void delegate() dg) {
  // calibrate
  int from1, to1, from2, to2;
  from1 = rdtsc[1];
  delegate void() { } ();
  to1 = rdtsc[1];
  // measure
  from2 = rdtsc[1];
  dg();
  to2 = rdtsc[1];
  writeln "$t: $((to2 - from2) - (to1 - from1))";
}

// ~1500 cycles
float noise3(vec3f v) {
  if !perm.length permsetup;
  auto s = (v.x + v.y + v.z) / 3.0f;
  // 180 cycles
  int i = fastfloor(v.x + s), j = fastfloor(v.y + s), k = fastfloor(v.z + s);
  auto t = (i + j + k) / 6.0f;
  auto V0 = vec3i(i, j, k) - vec3f(t);
  vec3f[4] vs = void;
  vs[0] = v - V0;
  
  vs[1] = vs[0]            + vec3f(1.0f / 6);
  vs[2] = vs[0]            + vec3f(2.0f / 6);
  vs[3] = vs[0] - vec3f(1) + vec3f(3.0f / 6);
  int mask = void;
  auto v0 = vs[0];
  if (v0.x >= v0.y) {
    if (v0.y >= v0.z) {
      mask = 0b100_110;
    } else if (v0.x >= v0.z) {
      mask = 0b100_101;
    } else {
      mask = 0b001_101;
    }
  } else {
    if (v0.y < v0.z) {
      mask = 0b001_011;
    } else if (v0.x < v0.z) {
      mask = 0b010_011;
    } else {
      mask = 0b010_110;
    }
  }
  auto offs1 = vec3i((mask >> 5)    , (mask >> 4) & 1, (mask >> 3) & 1);
  auto offs2 = vec3i((mask >> 2) & 1, (mask >> 1) & 1, (mask >> 0) & 1);
  vs[1] -= offs1;
  vs[2] -= offs2;
  int ii = i & 255, jj = j & 255, kk = k & 255;
  int[4] gi = void;
  alias i1 = offs1.x, i2 = offs2.x,
        j1 = offs1.y, j2 = offs2.y,
        k1 = offs1.z, k2 = offs2.z;
  gi[0] = perm[ii+perm[jj+perm[kk]]] % 12;
  gi[1] = perm[ii+i1+perm[jj+j1+perm[kk+k1]]] % 12;
  gi[2] = perm[ii+i2+perm[jj+j2+perm[kk+k2]]] % 12;
  gi[3] = perm[ii+1+perm[jj+1+perm[kk+1]]] % 12;
  float[4] n = void;
  for (int c = 0; c < 4; ++c) {
    auto q = vs[c];
    auto ft = 0.6f - q.x*q.x - q.y*q.y - q.z*q.z;
    if (ft < 0) n[c] = 0;
    else {
      ft *= ft;
      n[c] = ft * ft * dot3(grad3[gi[c]], q);
    }
  }
  return 0.5f + 16.0f*(n[0] + n[1] + n[2] + n[3]);
}
